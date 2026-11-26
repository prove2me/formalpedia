-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_discounted_polynomial_terminal_expectation_vanishes
-- name    : ManyServerQED.Scheduling.discounted_polynomial_terminal_expectation_vanishes
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:14:20.099135+00:00
-- url     : https://prove2.me/theorems/2d452e7a-a28a-4a60-b53c-5fe067c69751
-- title:
--   Vanishing discounted terminal expectations under polynomial moments
-- statement:
--   Suppose a state process has polynomial-in-time bounds for moments of every nonnegative integral order. For a twice continuously differentiable function of polynomial growth, every positively discounted terminal value is integrable, and its expectation tends to zero along integer horizons.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Diffusion
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.discounted_polynomial_terminal_expectation_vanishes
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (X : ℝ≥0 → Ω → Fin k → ℝ)
    (hX : ∀ t, Measurable (X t))
    (hMom : ∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ j : ℕ, ∀ t : ℝ≥0,
      Integrable (fun ω => l1norm (X t ω)^p) P ∧
      (∫ ω, l1norm (X t ω)^p ∂P) ≤ c*(1+(t:ℝ)^j))
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f) (γ : ℝ) (hγ : 0 < γ) :
    (∀ T : ℝ≥0, Integrable (fun ω => Real.exp (-γ*(T:ℝ)) * f (X T ω)) P) ∧
    Tendsto (fun T : ℕ => ∫ ω, Real.exp (-γ*(T:ℝ)) * f (X T ω) ∂P) atTop (𝓝 0) := by sorry
