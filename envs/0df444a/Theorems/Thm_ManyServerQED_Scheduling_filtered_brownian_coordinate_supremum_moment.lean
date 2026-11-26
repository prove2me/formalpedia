-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_filtered_brownian_coordinate_supremum_moment
-- name    : ManyServerQED.Scheduling.filtered_brownian_coordinate_supremum_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:19:49.874418+00:00
-- url     : https://prove2.me/theorems/413ee6d6-5fa2-5610-b2fc-91edc7dd0fc0
-- title:
--   Polynomial moment bounds for Brownian coordinate suprema
-- statement:
--   The supremum of the absolute value of a continuous filtered standard Brownian coordinate up to a fixed nonnegative time is measurable and its moment of every integer order greater than one is bounded by a polynomial in the horizon.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_filtered_brownian_coordinate_finite_sample_maximal_bound
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.filtered_brownian_coordinate_supremum_moment {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → Fin k → ℝ)
    (hW : IsStdFBrownian P F W)
    (hCont : ∀ ω, Continuous (fun t => W t ω)) (i : Fin k)
    (p : ℕ) (hp : 1 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ≥0,
      let S (ω : Ω) := ⨆ t : Iic T, ENNReal.ofReal |W t.1 ω i|
      Measurable S ∧ (∫⁻ ω, S ω^p ∂P) ≤ ENNReal.ofReal (A*(1+(T:ℝ))^p) := by sorry
