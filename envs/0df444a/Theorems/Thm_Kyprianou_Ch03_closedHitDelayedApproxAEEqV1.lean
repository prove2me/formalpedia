-- Prove2me | Theorems.Thm_Kyprianou_Ch03_closedHitDelayedApproxAEEqV1
-- name    : Kyprianou.Ch03.closedHitDelayedApproxAEEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:08:24.327661+00:00
-- url     : https://prove2.me/theorems/aa5e4ca6-d1e5-4a2b-8bdb-3230a11b3dad
-- title:
--   Positive-time closed hitting from delayed open approximations
-- statement:
--   For each positive delay, take the increasing limit of open-neighbourhood first entrance times. Quasi-left-continuity and closedness ensure that a finite limit hits the closed set. Finally take the infimum over reciprocal positive delays.
-- source:
--   Kyprianou (2006), Theorem 3.3, closed-set first hitting time.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.closedHitDelayedApproxAEEqV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (B : Set ℝ) (hB : IsClosed B)
    (hStop : ∀ j n : ℕ, IsStoppingTime F (fun w => sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 1 / ((j : NNReal) + 1) ≤ t ∧
        X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B}))) :
    ∀ᵐ w ∂P, Kyprianou.Ch03.firstHittingTime X B w =
      ⨅ j : ℕ, ⨆ n : ℕ, sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 1 / ((j : NNReal) + 1) ≤ t ∧
        X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B}) := by
  sorry
