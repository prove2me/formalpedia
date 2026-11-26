-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cutoffAEPointwiseBudgetV1
-- name    : Kyprianou.Ch04.cutoffAEPointwiseBudgetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:00:12.157896+00:00
-- url     : https://prove2.me/theorems/a8f1481a-b4e4-4dc4-89b5-c958ed11068b
-- title:
--   Common left-limit budget for nested-cutoff predictable kernels
-- statement:
--   Common left-limit budget for nested-cutoff predictable kernels
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem cutoffAEPointwiseBudgetV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (T : NNReal) (g : ℝ → ℝ → ℝ) (U V : NNReal → Ω → ℝ) (S : Ω → ℝ)
    (hG : ∀ s : ℝ, 0 ≤ s → Differentiable ℝ (g s))
    (hGbound : ∀ s x : ℝ, 0 ≤ s → |g s x| ≤ K)
    (hD : ∀ s x : ℝ, 0 ≤ s → |deriv (g s) x| ≤ K)
    (hLeft : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → t ≤ T →
      (U t ω - V t ω)^2 ≤ S ω) :
    ∀ᵐ ω ∂P, ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), ∀ z : ℝ,
      (({w : ℝ | a < |w| ∧ |w| < 1}).indicator
          (fun w => w * g s (U s.toNNReal ω)) z -
        ({w : ℝ | b < |w| ∧ |w| < 1}).indicator
          (fun w => w * g s (V s.toNNReal ω)) z)^2 ≤
      K^2 * (({w : ℝ | a < |w| ∧ |w| ≤ b ∧ |w| < 1}).indicator (fun w => w^2) z +
        ({w : ℝ | b < |w| ∧ |w| < 1}).indicator (fun w => w^2) z * S ω) := by
  sorry
end Kyprianou.Ch04
