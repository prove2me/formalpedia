-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Matrix_transferLoop_exec
-- name    : KoanaKPaths.Machine.Matrix.transferLoop_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:45.505166+00:00
-- url     : https://prove2.me/theorems/ed13c5ac-341a-489e-a552-af95b8b3d918
-- title:
--   Transferring a matrix of marked coordinate arrays
-- statement:
--   Suppose the current-layer stack holds marked arrays $A_1,\ldots,A_m$ above a tail, and the matrix counter contains $m$ unary markers. The transfer loop empties this counter, removes those frames from the current stack, and prepends the same arrays in reverse record order to the previous-layer stack:
--   $$\operatorname{Prev}_{\rm after}=\operatorname{frames}(A_m,\ldots,A_1)\mathbin{+\!+}\operatorname{Prev}_{\rm before}.$$
--   The order of coordinates within each array is preserved. Its exact time is $\operatorname{transferCost}(A_1,\ldots,A_m)$, summing one forward array-transfer charge and loop overhead per frame. Other registers, input position, output, and existing tails are preserved. This turns a completed current sketch layer into the next readonly matrix.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/MatrixTransfer.lean, line 28; source snapshot SHA-256 6181f3a7d4cfdf72e93f322ef26a6c49030660bf6d0ec25caf1652fb2b384d2a.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Matrix.transferLoop_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Matrix.NS) (arrays : List.{0} (List.{0} Int))
  (tail : List.{0} NLogN.Item)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Matrix.NS s KoanaKPaths.Machine.Matrix.Counter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} Int) arrays) NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Matrix.NS s KoanaKPaths.Machine.Matrix.Current)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames arrays) tail)),
  @NLogN.IExec KoanaKPaths.Machine.Matrix.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Matrix.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Matrix.transferLoop s
    (@NLogN.IState.upd KoanaKPaths.Machine.Matrix.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Matrix.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Matrix.NS s KoanaKPaths.Machine.Matrix.Counter
          (@List.nil.{0} NLogN.Item))
        KoanaKPaths.Machine.Matrix.Current tail)
      KoanaKPaths.Machine.Matrix.Prev
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames (@List.reverse.{0} (List.{0} Int) arrays))
        (@NLogN.IState.G KoanaKPaths.Machine.Matrix.NS s KoanaKPaths.Machine.Matrix.Prev)))
    (KoanaKPaths.Machine.Matrix.transferCost arrays) := by sorry
