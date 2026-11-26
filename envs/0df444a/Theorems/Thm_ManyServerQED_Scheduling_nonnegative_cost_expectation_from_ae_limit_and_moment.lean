-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_nonnegative_cost_expectation_from_ae_limit_and_moment
-- name    : ManyServerQED.Scheduling.nonnegative_cost_expectation_from_ae_limit_and_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:29:08.032174+00:00
-- url     : https://prove2.me/theorems/4b21aa69-cbbb-5c73-9204-09b6fcd74753
-- title:
--   Convergence of nonnegative cost expectations under a higher-moment bound
-- statement:
--   On a finite measure space, let nonnegative real random variables converge almost surely. If their moments of one fixed order greater than one are bounded uniformly from some index onward, the limiting variable is integrable and their expectations converge to its expectation.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem ManyServerQED.Scheduling.nonnegative_cost_expectation_from_ae_limit_and_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hZ : Measurable Z)
    (hy : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω) (hz : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (p : ℝ) (hp : 1 < p) (K : ℝ≥0∞) (hK : K < ⊤)
    (hMom : ∀ᶠ n in atTop, (∫⁻ ω, ENNReal.ofReal (Y n ω)^p ∂P) ≤ K) :
    Integrable Z P ∧
      Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂P) atTop
        (𝓝 (ENNReal.ofReal (∫ ω, Z ω ∂P))) := by sorry
