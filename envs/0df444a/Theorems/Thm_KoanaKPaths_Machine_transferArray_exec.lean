-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_transferArray_exec
-- name    : KoanaKPaths.Machine.transferArray_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:12:39.583391+00:00
-- url     : https://prove2.me/theorems/d9f9906b-99d1-44dc-bff0-5f023bc903b8
-- title:
--   Transferring a marked integer array without reversing its coordinates
-- statement:
--   Let source, destination, and temporary native registers be pairwise distinct. Suppose the source begins with a marked integer array $X$ above a tail. The array-transfer program consumes that frame and prepends an identical marked frame to the destination:
--   $$\operatorname{Src}=X\#T\longmapsto T,\qquad\operatorname{Dst}\longmapsto X\#\operatorname{Dst},\qquad t=2\operatorname{moveIntsCost}(X)+4.$$
--   The temporary stack is restored without an emptiness assumption, and all other native state, input position, and output are preserved. The move charge sums signed integer bit-transfer costs plus loop overhead. The result is a reusable order-preserving frame transfer for graph-sketch matrices and coordinate accumulators.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArrayTransfer.lean, line 16; source snapshot SHA-256 488a6a3288f0120b618fc025f375442c0bc4d536d9b9eec4e9138449af1d10f7.

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

theorem KoanaKPaths.Machine.transferArray_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst tmp : Fin S) (hsd : @Ne.{1} (Fin S) src dst)
  (hst : @Ne.{1} (Fin S) src tmp) (hdt : @Ne.{1} (Fin S) dst tmp) (s : NLogN.IState S) (xs : List.{0} Int)
  (tail : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark tail))),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.transferArray S src dst tmp) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark (@NLogN.IState.G S s dst))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (KoanaKPaths.Machine.moveIntsCost xs))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) := by sorry
