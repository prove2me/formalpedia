-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_transferBits_exec
-- name    : KoanaKPaths.Machine.transferBits_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:35.416942+00:00
-- url     : https://prove2.me/theorems/36ffd177-a98b-4f46-ac44-2b56d9b8a429
-- title:
--   Move a bit prefix with exact linear cost
-- statement:
--   Let source and destination be distinct raw-symbol stacks. Suppose the source begins with the encoded Boolean list $B$, followed by a tail whose first symbol is not a bit. The bit-transfer program removes exactly this prefix and produces
--   $$
--   \operatorname{src}'=\mathrm{tail},\qquad\operatorname{dst}'=\operatorname{reverse}(\operatorname{codeBits}B)\mathbin{+\!+}\operatorname{dst}.
--   $$
--   All other machine state is unchanged. The exact execution cost is
--   $$
--   4|B|+1.
--   $$
--   The source tail may be empty or begin with a nonbit delimiter. This is a raw-symbol movement statement, before conversion to the higher-level signed-integer item representation. It supplies the linear bit-copying component in the native natural-number parser and related stack encodings.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NatParser.lean, line 52; source snapshot SHA-256 32d4a7d75e6d80c6677b32667e0baf0b596da1ca06df35a5573c31039bb1cdc8.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.transferBits_exec :
∀ {S P : Nat} (I : List.{0} NLogN.Sym) (prog : Fin P → NLogN.Stmt S P) (src dst : Fin S) (hne : @Ne.{1} (Fin S) src dst)
  (σ : NLogN.St S) (A : List.{0} Bool) (tail : List.{0} NLogN.Sym)
  (ht : @Eq.{1} (Option.{0} Bool) (NLogN.bitOf (@List.head?.{0} NLogN.Sym tail)) (@Option.none.{0} Bool))
  (hs :
    @Eq.{1} (List.{0} NLogN.Sym) (@NLogN.St.stk S σ src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Sym) (List.{0} NLogN.Sym) (List.{0} NLogN.Sym)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Sym) (@List.instAppend.{0} NLogN.Sym))
        (@List.map.{0, 0} Bool NLogN.Sym NLogN.codeBit A) tail)),
  @NLogN.Exec S P I prog (@KoanaKPaths.Machine.transferBits S P src dst) σ
    (@NLogN.St.set S (@NLogN.St.set S σ src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Sym) (List.{0} NLogN.Sym) (List.{0} NLogN.Sym)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Sym) (@List.instAppend.{0} NLogN.Sym))
        (@List.map.{0, 0} Bool NLogN.Sym NLogN.codeBit (@List.reverse.{0} Bool A)) (@NLogN.St.stk S σ dst)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Bool A))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by sorry
