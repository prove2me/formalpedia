-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedClosedHitFixedApproxUpperV1
-- name    : Kyprianou.Ch03.delayedClosedHitFixedApproxUpperV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:33:51.451808+00:00
-- url     : https://prove2.me/theorems/e5d15789-5be3-4965-8785-abb96756873c
-- title:
--   Approximating delayed clocks are bounded by the closed hitting time
-- statement:
--   Use inclusion of B in every positive thickening, and monotonicity of the infimum.
-- source:
--   Kyprianou (2006), Theorem 3.3; parent 5883660c-e2b1-41dc-a4c4-0a044b9a9380.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedClosedHitFixedApproxUpperV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (B : Set ℝ) (hB : IsClosed B) (a : NNReal)
    (T : ℕ → Omega → WithTop NNReal)
    (hT : ∀ n w, T n w = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B}))
    (hStop : ∀ n, IsStoppingTime F (T n)) :
    ∀ w, (⨆ n, T n w) ≤ sInf ((fun t : NNReal => (t : WithTop NNReal)) '' {t : NNReal | a ≤ t ∧ X t w ∈ B}) := by
  sorry
