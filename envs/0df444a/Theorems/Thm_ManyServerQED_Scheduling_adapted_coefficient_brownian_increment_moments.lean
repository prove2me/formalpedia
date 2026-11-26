-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_adapted_coefficient_brownian_increment_moments
-- name    : ManyServerQED.Scheduling.adapted_coefficient_brownian_increment_moments
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:14:23.859429+00:00
-- url     : https://prove2.me/theorems/7d150090-0eea-4f72-bfd4-0808fd70df2a
-- title:
--   First and second moments of future Brownian increments against past coefficients
-- statement:
--   Let a standard vector Brownian motion be adapted to a filtration with independent future increments. A real coefficient measurable at time $s$ has zero integrated product with the increment of any coordinate over $[s,t]$. Its integrated product with two coordinate increments over that interval equals the expectation of the coefficient times $t-s$ on the diagonal and zero off the diagonal.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Diffusion
open MeasureTheory ProbabilityTheory Filter
open ManyServerQED.Scheduling
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.adapted_coefficient_brownian_increment_moments {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin k → ℝ) (hW : IsStdFBrownian P F W)
    (s t : ℝ≥0) (hst : s ≤ t) (A : Ω → ℝ) (hA : Measurable[F s] A) (i j : Fin k) :
    (∫ ω, A ω * (W t ω i - W s ω i) ∂P) = 0 ∧
      (∫ ω, A ω * ((W t ω i - W s ω i) * (W t ω j - W s ω j)) ∂P) =
        (if i = j then (t:ℝ) - (s:ℝ) else 0) * (∫ ω, A ω ∂P) := by sorry
