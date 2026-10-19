-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_approximation_center_exp_control
-- name    : OAI.PiExponent.MatrixArithmetic.approximation_center_exp_control
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T03:00:56.684971+00:00
-- url     : https://prove2.me/theorems/06cb00d6-802f-4312-9ee9-f833100cc03f
-- title:
--   Exponential normalization of a rational approximation center
-- statement:
--   A rational approximation with positive denominator gives an exponential bound for its complex center error after multiplication by any j ≤ K. Prove it from the exact norm identity, the approximation hypothesis, the exponential formula for real powers, and the ceiling bound for log q. The positivity and exponent-sign hypotheses preserve the inequality direction; j = 0, q = 1, and nu = 0 are included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Semiring

theorem OAI.PiExponent.MatrixArithmetic.approximation_center_exp_control
    (p : ℤ) (q j K : ℕ) (nu : ℝ)
    (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu) (hq : 1 ≤ q)
    (happrox : |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) *
      (2 * Complex.I * (p : ℂ) / (q : ℂ) -
        2 * Complex.I * (Real.pi : ℂ))‖ ≤
      Real.exp (Real.log (2 * (K : ℝ)) + nu -
        nu * (⌈Real.log (q : ℝ)⌉₊ : ℝ)) := by sorry
