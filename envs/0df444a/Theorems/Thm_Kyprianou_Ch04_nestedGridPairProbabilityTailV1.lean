-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nestedGridPairProbabilityTailV1
-- name    : Kyprianou.Ch04.nestedGridPairProbabilityTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:54:08.10183+00:00
-- url     : https://prove2.me/theorems/14c3adec-c5f4-5cd6-a4bc-424794d752e9
-- title:
--   nestedGridPairProbabilityTailV1
-- statement:
--   The nested cutoff maximal probability bound implies a cofinal probability estimate uniform in grid size.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.nestedGridPairProbabilityTailV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) (hν : IsLevyMeasure ν) (K : ℝ) (T : NNReal)
    (e : ℕ → ℝ) (he : ∀ m, 0 < e m) (he0 : Tendsto e atTop (𝓝 0))
    (A : ℕ → ℕ → ℕ → ℝ → Set Ω)
    (hB : ∀ m n l, e l < e m → ∀ δ : ℝ, 0 < δ →
      P (A m n l δ) ≤ ENNReal.ofReal (4 * ((K^2 * (T : ℝ) *
        (1 + 4 * (T : ℝ) * (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ e m}, ENNReal.ofReal (z^2) ∂ν).toReal)) /
        ENNReal.ofReal ((δ/2)^2)) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P (A m n l δ)).toReal ≤ η := by
  sorry
