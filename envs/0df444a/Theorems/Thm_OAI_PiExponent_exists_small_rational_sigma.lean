-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_small_rational_sigma
-- name    : OAI.PiExponent.exists_small_rational_sigma
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T09:05:39.745293+00:00
-- url     : https://prove2.me/theorems/65a1e0c8-2ccf-48b8-b28e-589eec73910f
-- title:
--   A small positive rational parameter satisfying three strict bounds
-- statement:
--   Let m be a natural number and let α, β, and θ be real numbers satisfying α < 1, β < 1, and θ < 1. No lower-bound or positivity assumptions on α, β, or θ are imposed. Then there exists a rational number σ > 0 such that (1 + 3σ)^(m+1)α < 1, (1 + 3σ)^mβ < 1, and (1 + σ)θ < 1, with σ viewed as a real number in these inequalities.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Sigma.lean#L7-L34

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

theorem OAI.PiExponent.exists_small_rational_sigma
    (m : ℕ) (α β θ : ℝ) (hα : α < 1) (hβ : β < 1) (hθ : θ < 1) :
    ∃ σ : ℚ, 0 < (σ : ℝ) ∧
      (1 + 3 * (σ : ℝ)) ^ (m + 1) * α < 1 ∧
      (1 + 3 * (σ : ℝ)) ^ m * β < 1 ∧
      (1 + (σ : ℝ)) * θ < 1 := by sorry
