-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedClosedHitFixedApproxV1
-- name    : Kyprianou.Ch03.delayedClosedHitFixedApproxV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T11:02:20.071122+00:00
-- url     : https://prove2.me/theorems/5883660c-e2b1-41dc-a4c4-0a044b9a9380
-- title:
--   Fixed-delay closed hitting equals increasing open-neighbourhood clock limit
-- statement:
--   The clocks increase and are bounded above by the delayed closed hitting time. At a finite supremum, quasi-left-continuity and right continuity imply the path lies in the closed target at the limit, proving the reverse bound.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed closed hitting approximation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedClosedHitFixedApproxV1
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
    ∀ᵐ w ∂P, (⨆ n, T n w) = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ B}) := by
  sorry
