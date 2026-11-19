-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_powerMarks_exec
-- name    : KoanaKPaths.Machine.powerMarks_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:20:27.3696+00:00
-- url     : https://prove2.me/theorems/ad55bae0-2eec-49c7-b7d8-f04ff50437f4
-- title:
--   Generating a power-of-two unary counter while preserving depth
-- statement:
--   Let four native registers for depth, count, control, and temporary storage be pairwise distinct. Suppose depth contains $d$ leading markers above a non-marker tail and the other three registers are empty. The power-markers program changes only the count register:
--   $$\operatorname{Count}_{\rm after}=\#^{2^d},\qquad t=1+(65d+60)+\operatorname{growMarksCost}(1,d).$$
--   It preserves the original depth, input position, output, and all other registers. The growth charge is defined by $G(m,0)=30$ and $G(m,d+1)=97m+91+G(2m,d)$. This gives an explicit native construction of the unary $2^d$ coordinate count needed to initialize and split exterior arrays.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativePowers.lean, line 79; source snapshot SHA-256 cb8f8408b9ec49b5f39e8c3b32d1bb0187ca79600e8b4f69ec46a44af9b7da21.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
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

theorem KoanaKPaths.Machine.powerMarks_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (depth count control tmp : Fin S) (hdc : @Ne.{1} (Fin S) depth count)
  (hdn : @Ne.{1} (Fin S) depth control) (hdt : @Ne.{1} (Fin S) depth tmp) (hcn : @Ne.{1} (Fin S) count control)
  (hct : @Ne.{1} (Fin S) count tmp) (hnt : @Ne.{1} (Fin S) control tmp) (s : NLogN.IState S) (d : Nat)
  (tail : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s depth)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item d NLogN.Item.mark) tail))
  (hc : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s count) (@List.nil.{0} NLogN.Item))
  (hn : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s control) (@List.nil.{0} NLogN.Item))
  (hx : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s tmp) (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.powerMarks S depth count control tmp) s
    (@NLogN.IState.upd S s count
      (@List.replicate.{0} NLogN.Item
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)
        NLogN.Item.mark))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65))) d)
          (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))))
      (KoanaKPaths.Machine.growMarksCost (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)) := by sorry
