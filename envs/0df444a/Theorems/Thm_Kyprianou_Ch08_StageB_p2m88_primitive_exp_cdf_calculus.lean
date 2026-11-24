-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_primitive_exp_cdf_calculus
-- name    : Kyprianou.Ch08.StageB.p2m88_primitive_exp_cdf_calculus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:06:46.279801+00:00
-- url     : https://prove2.me/theorems/6de66317-c5ef-41ab-93e7-57f1ec364b6f
-- title:
--   Exponential weight cancels a continuous primitive in a CDF formula
-- statement:
--   For any continuous-on-the-nonnegative-half-line function w and a function f satisfying f(b)=q/phi*w(b)-q times its primitive from zero, integration by parts cancels the primitive terms in the weighted cumulative expression.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, integration by parts of the negative-infimum law.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Exponential weight cancels a continuous primitive in a CDF formula -/
theorem p2m88_primitive_exp_cdf_calculus :
    ∀ (φ q : ℝ) (w f : ℝ → ℝ),
      0 < φ → 0 < q → ContinuousOn w (Ici (0 : ℝ)) →
      (∀ b : ℝ, 0 ≤ b → f b =
        q / φ * w b - q * ∫ s in (0 : ℝ)..b, w s) →
      ∀ b : ℝ, 0 ≤ b →
      Real.exp (-φ * b) * f b +
        φ * (∫ t in (0 : ℝ)..b, Real.exp (-φ * t) * f t) =
      q / φ * Real.exp (-φ * b) * w b := by
  sorry

end Kyprianou.Ch08.StageB
