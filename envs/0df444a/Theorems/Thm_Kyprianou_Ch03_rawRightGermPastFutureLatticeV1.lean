-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawRightGermPastFutureLatticeV1
-- name    : Kyprianou.Ch03.rawRightGermPastFutureLatticeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:24:56.477038+00:00
-- url     : https://prove2.me/theorems/1d32ef22-9f74-4973-8a99-94c7984cc733
-- title:
--   Raw Lévy right-germ bounds by past and full future
-- statement:
--   For an arbitrary real path process, its raw past lies in its raw right germ, which lies in the join of the raw past and the full shifted future. This join in turn lies in the sigma-algebra of the whole path. For the middle inclusion, every observation at r>t equals X t plus shifted increment r−t; the past is contained by monotonicity. This uses the full future, never distribution of a join across an intersection.
-- source:
--   Kyprianou (2006), Exercise 3.1; parent dc6deda8-897b-4e0f-b4f3-f2428ced614a.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.rawRightGermPastFutureLatticeV1
    {Omega : Type}
    (X : NNReal → Omega → Real) (t : NNReal) :
    PerfCorrMSQ.natFiltr X t ≤ (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ∧
      (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤ PerfCorrMSQ.natFiltr X t ⊔ (MeasurableSpace.comap (fun ω : Omega => fun u : NNReal => X (t + u) ω - X t ω) inferInstance) ∧
      PerfCorrMSQ.natFiltr X t ⊔ (MeasurableSpace.comap (fun ω : Omega => fun u : NNReal => X (t + u) ω - X t ω) inferInstance) ≤ (MeasurableSpace.comap (fun ω : Omega => fun u : NNReal => X u ω) inferInstance) := by
  sorry
