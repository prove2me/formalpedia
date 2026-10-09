-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_large_log_approximation
-- name    : OAI.PiExponent.exists_large_log_approximation
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:57:48.04589+00:00
-- url     : https://prove2.me/theorems/10b40ea4-71eb-4ac0-a8af-a5fc040e0189
-- title:
--   Large-denominator approximation under a uniform power-law approximation hypothesis
-- statement:
--   Let ν and X be real numbers with ν > 0. Assume that for every natural number Q there are an integer p and a natural number q such that Q ≤ q and |π − p/q| ≤ q^(−ν). Then there are an integer p and a natural number q with 2 ≤ q, X < log q, p ≠ 0, and |π − p/q| ≤ q^(−ν). The approximation hypothesis is part of the theorem's assumptions; this statement does not assert unconditionally that such approximations exist.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/ApproximationSelection.lean#L8-L31

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

theorem OAI.PiExponent.exists_large_log_approximation
    (nu X : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ,
      2 ≤ q ∧ X < Real.log q ∧ p ≠ 0 ∧
        |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by sorry
