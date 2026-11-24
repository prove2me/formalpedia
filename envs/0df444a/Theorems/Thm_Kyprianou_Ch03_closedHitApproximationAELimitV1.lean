-- Prove2me | Theorems.Thm_Kyprianou_Ch03_closedHitApproximationAELimitV1
-- name    : Kyprianou.Ch03.closedHitApproximationAELimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:08:31.101031+00:00
-- url     : https://prove2.me/theorems/dcfd123c-ffbd-46b9-aae7-87cfae8c104d
-- title:
--   Closed hitting time as a limit of open approximating clocks
-- statement:
--   For each positive cutoff a_m=1/(m+1), the increasing open-neighbourhood hitting clocks have a supremum. If finite, it is at least a_m>0. Right continuity puts each finite stopped value in the closure of its neighbourhood; the Proved quasi-left-continuity theorem identifies the limit value in B. The limiting clock bounds the first positive closed hit from above, while every positive closed hit dominates all the approximating clocks for a sufficiently small cutoff. Take the infimum over m. Empty hitting sets have extended infimum top.
-- source:
--   Kyprianou (2006), Theorem 3.3; closed hitting child 567fb35e-7763-499a-b65a-6ab9d41e8485.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.closedHitApproximationAELimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsClosed B)
    (hStop : ∀ m n : ℕ, IsStoppingTime F (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
      (1 / ((m : NNReal) + 1)) < r ∧
      X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B ∧
      u = (r : WithTop NNReal)})) :
    firstHittingTime X B =ᵐ[P] (fun w : Omega => ⨅ m : ℕ, ⨆ n : ℕ, (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
      (1 / ((m : NNReal) + 1)) < r ∧
      X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B ∧
      u = (r : WithTop NNReal)}) w) := by
  sorry
