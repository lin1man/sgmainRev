from idc import *
from idaapi import *
from idautils import *
from Crypto.Cipher import ARC4
from capstone import *
from capstone.arm import *

def str_bytearray(str):
    return ' '.join(hex(x) for x in bytearray(str))

def put_unconditional_branch(source, destination):
    offset = (destination - source - 4) >> 1
    if offset > 2097151 or offset < -2097152:   # 0x200000 2MB
        raise RuntimeError("Invalid offset")
    if offset > 1023 or offset < -1024:
        instruction1 = 0xf000 | ((offset >> 11) & 0x7ff)
        instruction2 = 0xb800 | (offset & 0x7ff)
        patch_word(source, instruction1)
        patch_word(source + 2, instruction2)
    else:
        instruction = 0xe000 | (offset & 0x7ff)
        patch_word(source, instruction)


def put_bl_branch(source, destination):
    offset = (destination - source - 4 - 2) >> 1        #4 for pc, 2 for PUSH {LR}
    if offset > 2097151 or offset < -2097152:   # 0x200000 2MB
        raise RuntimeError("Invalid offset")
    instruction1 = 0xb500                               #PUSH {LR}
    instruction2 = 0xf000 | ((offset >> 11) & 0x7ff)    #BL imm10
    instruction3 = 0xf800 | (offset & 0x7ff)            #BL imm11   imm32=signExtend(s:0:0:imm10:imm11:'0',32)
    instruction4 = 0xbd00                               #PUSH {PC}
    patch_word(source, instruction1)
    patch_word(source+2, instruction2)
    patch_word(source+4, instruction3)
    patch_word(source+6, instruction4)



def rc4Decrypt():
    ea = here()
    length = ask_long(1,"Specify length")
    if length > 1:
        rc4 = ARC4.new("DcO/lcK+h?m3c*q@")
        str = rc4.decrypt(get_bytes(ea, length))
        MakeComm(ea, str)


def cs_disasm(arch, mode, code, offset):
    try:
        md = Cs(arch, mode)
        md.detail = True
        inss = []
        for insn in md.disasm(code, offset):
            inss.append(insn)
        return inss
    except CsError as e:
        return None

def cs_arm_thumb(code, offset=0x80000000):
    return cs_disasm(CS_ARCH_ARM, CS_MODE_THUMB, code, offset)


def cs_arm_arm(code, offset=0x80000000):
    return cs_disasm(CS_ARCH_ARM, CS_MODE_ARM, code, offset)

def plog(msg):
    print(msg)

def plogi(ea, msg):
    plog("[Info ] %08x : %s" % (ea, msg))

def plogic(ea, msg):
    MakeCode(ea)
    plog("[Info ] %08x : %s" % (ea, msg))

def plogw(ea, msg):
    plog("[Warn ] %08x : %s" % (ea, msg))

def ploge(ea, msg):
    plog("[Error] %08x : %s" % (ea, msg))

def align_down(x, size=4):
    return x & ~(size - 1)

def align_up(x, size=4):
    return (x + size - 1) & ~(size - 1)

def get_s8(val):
    if val < 0x80:
        return val
    else:
        return (val - 0x100)

def get_s16(val):
    if val < 0x8000:
        return val
    else:
        return (val - 0x10000)

def get_s24(val):
    if val < 0x800000:
        return val
    else:
        return (val - 0x1000000)

def get_s32(val):
    if val < 0x80000000:
        return val
    else:
        return (val - 0x100000000)

def getAdrRegValueT1(ins): #ADR Rd,#  10100dddmmmmmmmm Rd=(ddd) mmmmmmmm:'00'
    return ((ins & 0x0700) >> 8), ((ins & 0xff) << 2)

def getSubsRegValueT2(ins): #SUBS Rdn,#<imm8>   00111{nnn}{imm8}
    return ((ins & 0x0700) >> 8), (ins & 0xff)

def getAddsRegValueT2(ins): #ADDS Rdn,#<imm8>   00110{nnn}{imm8}
    return ((ins & 0x0700) >> 8), (ins & 0xff)

def getLdrRegValueT1(ins):  #LDR Rn,#<imm8:'00'>
    return ((ins & 0x0700) >> 8), ((ins & 0xff) << 2)

def patchPushSubsAdds(ea):
    if get_wide_word(ea) == 0xb507 and get_wide_word(ea+18) == 0xbd07: #PUSH {R0-R2,LR} POP {R0-R2,PC}
        ins1 = get_wide_word(ea+2)  #ADR Rn,#<imm8>
        ins2 = get_wide_word(ea+6)  #SUBS Rn,#<imm8>
        ins3 = get_wide_word(ea+14) #ADDS Rn,#<imm8>
        ins4 = get_wide_word(ea+16) #STR Rn,[SP,#<imm8>]
        address = ea+4
        # ADR Rn,#imm1  STR Rn,[SP,#0xc]  STR(T2):10010{ttt}{imm8} STR Rt,[sp,imm8:'00'}
        if (ins1 & 0xa800) == 0xa000 and (ins4 & 0xf8ff) == 0x9003:
            if (ins2 & 0xf800) == 0x3800 and (ins3 & 0xf800) == 0x3000: #SUBS ADDS
                reg1,imm1 = getAdrRegValueT1(ins1)
                reg2,imm2 = getSubsRegValueT2(ins2)
                reg3,imm3 = getAddsRegValueT2(ins3)
                if reg1 != 1 or reg2 != 1 or reg3 != 0:
                    plogw(ea, "reg umatch %d %d %d" % (reg1, reg2, reg3))
                address += imm1
                address -= imm2
                address += imm3
                put_unconditional_branch(ea, address)
                plogic(ea, "patch push sub add")
            else:
                ploge(ea," may be can patch by patchPushSubsAdds")

def patch494c(ea):
    if get_wide_word(ea) == 0xb503: #PUSH {R0,R1,LR}
        ea1 = ea + 2
        if get_wide_word(ea1) == 0xbf00: #NOP
            ea1 += 2
        ins1 = get_wide_word(ea1)
        if (ins1 & 0xff00) == 0x4800:   #LDR R0,=XX
            reg1,imm1 = getLdrRegValueT1(ins1)  #LDR R0,
            index = get_wide_dword(align_up(ea1+2+imm1))
            ea1 += 2
            ins2 = get_wide_word(ea1)
            ins2_dw = get_wide_dword(ea1)
            table = None
            if (ins2 & 0xff00) == 0x4900:   #LDR R1,=xxx
                ea1 +=2
                inss = cs_arm_thumb(get_bytes(ea1,4), ea1)
                if inss:
                    if inss[0].operands[0].imm == 0x494c:
                        table = ea1 + 4
                if table == None:
                    ploge(ea, "may be bl 494c,but not find BLX 494c")
            elif (ins2_dw & 0xc000f800) == 0xc000f000:  #BL T1 11110S{imm10} 11{j1}1{j2}{imm11}  BLX T2 11110S{imm10H} 11{j1}0{j2}{imm10L}H
                inss = cs_arm_thumb(get_bytes(ea1,4), ea1)
                if inss:
                    blInsEa = inss[0].operands[0].imm
                    inss2 = cs_arm_thumb(get_bytes(blInsEa, 4), blInsEa)
                    if inss2:
                        if inss2[0].operands[0].imm == 0x494c:
                            table = blInsEa + 4
                if table == None:
                    ploge(ea, "may be bl 494c,but find bl 494c error")
            if table:
                offset = get_wide_dword(table + (index << 2))
                put_unconditional_branch(ea, table + offset)
                plogic(ea, "patch BLX 494c")

def patchPushAdrBLAddsPop(ea):
    ins1 = get_wide_word(ea)
    if (ins1 & 0xf700) == 0xb500 and (get_wide_word(ea+16) & 0xf7ff) == ins1: #PUSH {X-X,LR} POP {X-X,PC}
        if get_wide_dword(ea+6) == 0xf800f000:  #BL 0
            ins2 = get_wide_word(ea+2)
            ins3 = get_wide_word(ea+10)
            if (ins3 & 0xf800) == 0x3000: #ADDS
                reg2,imm2 = getAdrRegValueT1(ins2)
                reg3,imm3 = getAddsRegValueT2(ins3)
                if reg2 != reg3:
                    ploge(ea, "may be Push BL 0 Pop,but reg not equal")
                else:
                    address = ea + 4 + imm2 + imm3
                    put_unconditional_branch(ea, address)
                    plogic(ea, "patch Push BL 0 Pop")
            else:
                ploge(ea, "may be Push BL 0 Pop")

def patchPushAdrMovsBeqBne(ea):
    if (get_wide_word(ea) & 0xff00) == 0xb500:
        ins1 = get_wide_word(ea+12)
        ins2 = get_wide_word(ea+14)
        if (ins1 & 0xff00) == 0xd000 and (ins2 & 0xff00) == 0xd100: #BEQ BNE
            if (ins1 & 0xfe) == (ins2 & 0xfe): # BNE BEQ to same
                ins3 = get_wide_word(ea + 2)    #ADR R4,
                ins4 = get_wide_word(ea + 4)    #MOVS R5,#2
                ins5 = get_wide_word(ea + 6)    #ADDS R5,#n
                reg3,imm3 = getAdrRegValueT1(ins3)
                if ins4 != 0x2502 or reg3 != 4 or (ins5 & 0xff00) != 0x3500:
                    plogw(ea, "may be Push Adr Movs Beq Bne but not ADR R4,#x MOVS R5,#n")
                address = ea + 4 + imm3 + (ins4 & 0xff) + (ins5 & 0xff)
                put_unconditional_branch(ea, address)
                plogic(ea, "patch Push Adr Movs Beq Bne")
            else:
                plogw(ea, "may be Push Adr Movs Beq Bne")

def patchSubPushBlx4964(ea):
    patches = {}
    # LDR(literal)      T1 01001ttt{imm8}       LDR Rt,<label>  pc+imm8:'00'
    # LDR(immediate)    T1 01101{imm5}nnnttt    LDR Rt,[Rn{,#<imm>}] imm32=imm5:'00'
    # B                 T2 11100{imm11}         B <label>   imm32=imm11:'0'
    patches[0]  = (0x01,0x48,0x00,0x68) #,0x02,0xe0
    patches[1]  = (0x01,0x49,0x09,0x68) #,0x02,0xe0
    patches[2]  = (0x01,0x4a,0x12,0x68) #,0x02,0xe0
    patches[3]  = (0x01,0x4b,0x1b,0x68) #,0x02,0xe0
    patches[4]  = (0x01,0x4c,0x24,0x68) #,0x02,0xe0
    patches[5]  = (0x01,0x4d,0x2d,0x68) #,0x02,0xe0
    patches[6]  = (0x01,0x4e,0x36,0x68) #,0x02,0xe0
    patches[7]  = (0x01,0x4f,0x3f,0x68) #,0x02,0xe0
    # LDR(literal)      T2 11111000 U1011111 tttt{imm12}        LDR Rt,<label>
    # LDR(immediate)    T3 11111000 1101nnnn tttt{imm12}        LDR Rt,[Rn{,#<imm12>}]
    # B                 T2 11100{imm11}         B <label>   imm32=imm11:'0'
    patches[8]  = (0xdf,0xf8,0x08,0x80,0xd8,0xf8,0x00,0x80) #,0x01,0xe0
    patches[9]  = (0xdf,0xf8,0x08,0x90,0xd9,0xf8,0x00,0x90) #,0x01,0xe0
    patches[10] = (0xdf,0xf8,0x08,0xa0,0xda,0xf8,0x00,0xa0) #,0x01,0xe0
    patches[11] = (0xdf,0xf8,0x08,0xb0,0xdb,0xf8,0x00,0xb0) #,0x01,0xe0
    patches[12] = (0xdf,0xf8,0x08,0xc0,0xdc,0xf8,0x00,0xc0) #,0x01,0xe0
    patches[13] = (0xdf,0xf8,0x08,0xd0,0xdd,0xf8,0x00,0xd0) #,0x01,0xe0
    patches[14] = (0xdf,0xf8,0x08,0xe0,0xde,0xf8,0x00,0xe0) #,0x01,0xe0
    if get_wide_word(ea) == 0xb082 and get_wide_word(ea+2) == 0xb503: #SUB SP,SP,#8 PUSH {R0,R1,LR}
        ins1 = get_wide_dword(ea+4)
        if (ins1 & 0xc000f800) == 0xc000f000:  # BL T1 11110S{imm10} 11{j1}1{j2}{imm11}  BLX T2 11110S{imm10H} 11{j1}0{j2}{imm10L}H
            ea1 = ea + 4
            inss = cs_arm_thumb(get_bytes(ea1, 4), ea1)
            if inss:
                blInsEa = inss[0].operands[0].imm
                if blInsEa == 0x4964:
                    if (get_wide_word(ea+12) & 0xff00) == 0xbc00:   # POP {Rn}
                        register = -1
                        r = get_wide_byte(ea+12)
                        for i in range(8):
                            if r == (1 << i):
                                register = i
                                break
                        if register == -1:
                            ploge(ea, "BLX 4964 register detect error:{%02x}" % r)
                        else:
                            address = get_wide_dword(ea+8)+ea+8
                            ea3 = ea
                            if (ea3 % 4) == 0:
                                patch_word(ea3, 0xbf00)  # nop
                                ea3 += 2
                            for b in patches[register]:
                                patch_byte(ea3, b)
                                ea3 += 1
                            if (ea3 - ea) == 4:         #total:14
                                patch_word(ea3, 0xe003) #BL 3*2+2  address+4
                            elif (ea3 - ea) == 6:       #total:14
                                patch_word(ea3, 0xe002)
                            else: #show not exist
                                ploge(ea, "patch BLX 4964 error")
                                return
                            ea3 += 2
                            patch_dword(ea3, address)
                            plogic(ea, "patch BLX 4964")
                    else:
                        ins2 = get_wide_dword(ea+12)
                        #LDR T4  11111000 0101nnnn tttt1PUW{imm8}
                        if (ins2 & 0x0fffffff) == 0x0b04f85d: #LDR.w Rt,[sp],#4
                            register = (ins2 >> 28) & 0x0f
                            if register in patches:
                                address = get_wide_dword(ea + 8) + ea + 8
                                ea2 = ea
                                if (ea2 % 4) == 0:
                                    patch_word(ea2, 0xbf00)  #nop
                                    ea2 += 2
                                for b in patches[register]:
                                    patch_byte(ea2, b)
                                    ea2 += 1
                                if (ea2 - ea) == 8:         #total:16
                                    patch_word(ea2, 0xe002)
                                elif (ea2 - ea) == 10:      #total:16
                                    patch_word(ea2, 0xe001)
                                elif (ea2 - ea) == 4:       # total:16
                                    patch_word(ea2, 0xe004) # BL 3*2+2  address+4
                                elif (ea2 - ea) == 6:       # total:16
                                    patch_word(ea2, 0xe003)
                                else:  # show not exist
                                    ploge(ea, "patch BLX 4964 error")
                                    return
                                ea2 += 2
                                patch_dword(ea2, address)
                                plogic(ea, "patch BLX 4964")
                            else:
                                plogw(ea, "BLX 4964 register error:{%d}" % register)
                        else:
                            plogw(ea, "may be like BLX 4964, but ldr unknown")
                else:
                    plogi(ea, "may be like BLX 4964")

def patchPushPushMovsAdd(ea):
    if (get_wide_word(ea) & 0xff00) == 0xb500 and (get_wide_word(ea+2) & 0xff00) == 0xb500: #PUSH {Rn-Rx,LR} PUSH {Rn-Rx,LR}
        ins1 = get_wide_word(ea+30) # STR R6,[R0,#24]   T1  01100{imm5}nnnttt    STR Rt,[Rn{,#<imm>}]   imm32=imm5:'00'
        ins2 = get_wide_word(ea+32) # POP {R6}          T1  1011110P{reg_list}  POP <register>
        ins3 = get_wide_word(ea+34) # B
        if (ins1 & 0xf800) == 0x6000 and (ins2 & 0xff00) == 0xbc00 and (ins3 & 0xff00) == 0xe000:
            ins4 = get_wide_word(ea+20) # ADR R6,#      T1  10100ddd{imm8}  ADR Rd,<label>  imm32=imm8:'00'
            ins5 = get_wide_word(ea+24) # MOVS R1,#     T1  00100ddd{imm8}  MOVS Rd,#imm8   imm32=ZeroExtend(imm8)
            ins6 = get_wide_word(ea+26) # ADDS R6,#     T2  00110nnn{imm8}  ADDS Rd,#imm8   imm32=ZeroExtend(imm8)
            if (ins4 & 0xff00) != 0xa600 or (ins5 & 0xff00) != 0x2100 or (ins6 & 0xff00) != 0x3600:
                plogw(ea, "may be Push Push Movs Add")
            address = ((ins4 & 0xff) << 2) + 4 + ea + 20 + 1
            address += (ins5 & 0xff) + (ins6 & 0xff)
            put_unconditional_branch(ea, address)
            plogic(ea, "patch Push Push Movs Add b %08x" % address)

def patchPushBlBlPushAddAddAddPop(ea):
    if (get_wide_word(ea) & 0xff00) == 0xb500 and get_wide_dword(ea+10) == 0xf802f000 and get_wide_dword(ea+14) == 0xe800f000: #PUSH {,LR} bl 6  bl 0
        ins1 = get_wide_word(ea+2)  # ADR R4,#      T1  10100ddd{imm8}  ADR Rd,<label>  imm32=imm8:'00'
        ins2 = get_wide_word(ea+4)  # SUBS R4,#     T2  00111ddd{imm8}  SUB Rd,#<imm8>  imm32=imm8
        ins3 = get_wide_word(ea+24) # ADDS R0,R0,#4 T1  0001110{imm3}nnnddd ADDS Rd,Rn,#imm3
        ins4 = get_wide_word(ea+26) # ADDS R0,#0xc  T2  00110ddd{imm8}  ADDS Rd,#<imm8>
        ins5 = get_wide_word(ea+28) # ADDS R0,R0,#7 T1  0001110{imm3}nnnddd ADDS Rd,Rn,#imm3
        if (ins3 & 0xfe3f) != 0x1c00 or (ins4 & 0xff00) != 0x3000 or (ins5 & 0xfe3f) != 0x1c00:
            plogw(ea, "may be Push BL BL Push Add Add Add Pop")
        address = ((ins1 & 0xff) << 2) + ea + 4
        address -= ins2 & 0xff
        address += (ins3 >> 6) & 0x7
        address += ins4 & 0xff
        address += (ins5 >> 6) & 0x7
        put_unconditional_branch(ea, address)
        plogic(ea, "patch Push BL BL Push Add Add Add Pop b %08x" % address)

def patchPushBlx4998(ea):
    if get_wide_word(ea) == 0xb503:
        ea1 = ea+2
        if get_wide_word(ea1) == 0xbf00: #NOP
            ea1 += 2
        ins1 = get_wide_dword(ea1)
        if (ins1 & 0xc000f800) == 0xc000f000:  # BL T1 11110S{imm10} 11{j1}1{j2}{imm11}  BLX T2 11110S{imm10H} 11{j1}0{j2}{imm10L}H
            inss = cs_arm_thumb(get_bytes(ea1, 4), ea1)
            if inss:
                if inss[0].operands[0].imm == 0x4998:
                    address = get_s32(get_wide_dword(ea1+4)) + ea1 + 4
                    put_unconditional_branch(ea, address)
                    plogic(ea, "patch BLX 4998 b %08x" % address)
                else:
                    plogw(ea, "like blx 4998")
            else:
                plogw(ea, "like blx 4998")

def patchLdrRtLabel(ea, rt, label):
    offset = label - ea - 2
    if (offset > 4096) or (offset < -4096):
        raise RuntimeError("Invalid offset, LDR, Rt,label")
    if offset >= 0:
        patch_byte(ea, 0xdf)
    else:
        patch_byte(ea, 0x5f)
    patch_byte(ea+1, 0xf8)
    patch_byte(ea+2, offset & 0xff)
    patch_byte(ea+3, ((offset >> 8) & 0xf) | (rt << 4))

def patchSubspPushBl4a04(ea): #todo no space
    if get_wide_word(ea) == 0xb083 and get_wide_word(ea+2) == 0xb503:   # SUB SP,SP,#0xC PUSH {R0,R1,LR}
        ea1 = ea + 4
        if get_wide_word(ea1) == 0xbf00: # nop
            ea1 += 2
        ins1 = get_wide_dword(ea1)
        if (ins1 & 0xc000f800) == 0xc000f000:  # BL T1 11110S{imm10} 11{j1}1{j2}{imm11}  BLX T2 11110S{imm10H} 11{j1}0{j2}{imm10L}H
            inss = cs_arm_thumb(get_bytes(ea1, 4), ea1)
            if inss:
                if inss[0].operands[0].imm == 0x4a04:
                    address = get_s32(get_wide_dword(ea1+4)) + ea1 + 4
                    patchLdrRtLabel(ea, 0, address)
                    patchLdrRtLabel(ea+4, 1, address + 4)

patch_start=0x0000
patch_end=0x886e0
for ea in range(patch_start, patch_end):
    #patchPushSubsAdds(ea)
    #patch494c(ea)
    #patchPushAdrBLAddsPop(ea)
    #patchPushAdrMovsBeqBne(ea)
    #patchSubPushBlx4964(ea)
    #patchPushPushMovsAdd(ea)
    #patchPushBlBlPushAddAddAddPop(ea)

    #patchPushBlx4998(ea)
    pass

ea = here()


print("PatchBlukEnd")