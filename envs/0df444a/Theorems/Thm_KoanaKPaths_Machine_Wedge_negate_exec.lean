-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Wedge_negate_exec
-- name    : KoanaKPaths.Machine.Wedge.negate_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:57.989706+00:00
-- url     : https://prove2.me/theorems/4818e141-d30f-46f2-a0d9-1ef0e606afa0
-- title:
--   Negate a framed coefficient array in place with exact cost
-- statement:
--   Let an integer array $X=[x_1,\ldots,x_m]$ occupy a marked frame on a stack distinct from the negation temporary stack. The native array-negation program replaces the frame by
--   $$
--   -X=[-x_1,\ldots,-x_m]
--   $$
--   in the same coordinate order, preserving its delimiter, saved tail, temporary stack and all unrelated state. Its exact execution cost is
--   $$
--   2C_{\rm move}(X)+20m+3,
--   $$
--   where $C_{\rm move}(X)=30+\sum_j(2\mu(\beta(x_j))+49)$, $\beta$ is integer width and $\mu$ is the primitive integer-move charge. No sign or magnitude hypothesis is required on the coefficients. This operation implements the sign reversal needed when assembling the upper block of a recursive exterior product.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/WedgeNativeCorrect.lean, line 45; source snapshot SHA-256 d871d5f6d5e3726310a18d11b17aa599372eba036b56fb41a12f7ca67f1521c6.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
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

theorem KoanaKPaths.Machine.Wedge.negate_exec :
∀ (I : List.{0} NLogN.Sym) (src : Fin KoanaKPaths.Machine.Wedge.NS)
  (hne : @Ne.{1} (Fin KoanaKPaths.Machine.Wedge.NS) src KoanaKPaths.Machine.Wedge.Z)
  (s : NLogN.IState KoanaKPaths.Machine.Wedge.NS) (xs : List.{0} Int) (tail : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark tail))),
  @NLogN.IExec KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog (KoanaKPaths.Machine.Wedge.negate src) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Wedge.NS s src
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item (fun (z : Int) => NLogN.Item.int (@Neg.neg.{0} Int Int.instNegInt z)) xs)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark tail)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (KoanaKPaths.Machine.moveIntsCost xs))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) (@List.length.{0} Int xs)))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := by sorry
