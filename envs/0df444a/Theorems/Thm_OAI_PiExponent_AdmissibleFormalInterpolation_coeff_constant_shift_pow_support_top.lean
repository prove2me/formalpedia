-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_constant_shift_pow_support_top
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support_top
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:26:26.480344+00:00
-- url     : https://prove2.me/theorems/8d024f33-91b0-4281-8a9a-e978319e4b1d
-- title:
--   Support and top coefficient of a constant-shifted coordinate power
-- statement:
--   For every exponent, the shifted coordinate power has coefficient one at its top exponent, and all its nonzero coefficients have exponent vectors bounded componentwise by that top exponent. This includes exponent zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support_top
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (a : R) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single x n)
        ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) = 1 ∧
      ∀ k : σ →₀ ℕ,
        MvPowerSeries.coeff k ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) ≠ 0 →
          k ≤ Finsupp.single x n := by sorry
