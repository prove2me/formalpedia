-- Prove2me | Theorems.Thm_Kyprianou_Ch04_weightedCutoffIntegratedBudgetV1
-- name    : Kyprianou.Ch04.weightedCutoffIntegratedBudgetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:58:06.941003+00:00
-- url     : https://prove2.me/theorems/53fcf3ba-ddbe-5399-9162-98a17d86b640
-- title:
--   Integrated nested cutoff predictable energy estimate
-- statement:
--   Integrated nested cutoff predictable energy estimate
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem weightedCutoffIntegratedBudgetV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (T : NNReal) (g : ℝ → ℝ → ℝ) (U V : NNReal → Ω → ℝ) (S : Ω → ℝ)
    (hG : ∀ s : ℝ, 0 ≤ s → Differentiable ℝ (g s))
    (hGbound : ∀ s x : ℝ, 0 ≤ s → |g s x| ≤ K)
    (hD : ∀ s x : ℝ, 0 ≤ s → |deriv (g s) x| ≤ K)
    (hS : Integrable S P) (hSnn : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (hLeft : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → t ≤ T →
      (U t ω - V t ω)^2 ≤ S ω)
    (hEnergy : (∫ ω, S ω ∂P) ≤ 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    (∫ ω, ∫ s in Ioc (0 : ℝ) (T : ℝ),
      ∫ z, (({w : ℝ | a < |w| ∧ |w| < 1}).indicator
          (fun w => w * g s (U s.toNNReal ω)) z -
        ({w : ℝ | b < |w| ∧ |w| < 1}).indicator
          (fun w => w * g s (V s.toNNReal ω)) z)^2 ∂ν ∂volume ∂P) ≤
      (K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
        (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal := by
  sorry
end Kyprianou.Ch04
