-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedClosedHitFixedApproxLowerV1
-- name    : Kyprianou.Ch03.delayedClosedHitFixedApproxLowerV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:33:52.402901+00:00
-- url     : https://prove2.me/theorems/62f54ab9-0043-4237-8181-2219d72a2821
-- title:
--   Closed hitting time is bounded by the supremum of delayed clocks
-- statement:
--   Monotonicity in n, stopping-time supremum, quasi-left-continuity at its finite limit, and right-continuity at each approximating time identify a closed hit at the limiting clock.
-- source:
--   Kyprianou (2006), Theorem 3.3; parent 5883660c-e2b1-41dc-a4c4-0a044b9a9380.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedClosedHitFixedApproxLowerV1
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
    ∀ᵐ w ∂P, sInf ((fun t : NNReal => (t : WithTop NNReal)) '' {t : NNReal | a ≤ t ∧ X t w ∈ B}) ≤ (⨆ n, T n w) := by
  sorry
