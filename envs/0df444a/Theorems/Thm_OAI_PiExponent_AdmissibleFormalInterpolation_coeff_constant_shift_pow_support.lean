-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_constant_shift_pow_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:31:11.956194+00:00
-- url     : https://prove2.me/theorems/da3b2b90-5319-4c42-a0dc-5b91b6975e85
-- title:
--   Support bound for a constant-shifted coordinate power
-- statement:
--   Every exponent with a nonzero coefficient in the nth power of `X x + C a` is componentwise at most `Finsupp.single x n`, including when `n = 0`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (a : R) (n : ℕ) :
    ∀ k : σ →₀ ℕ,
      MvPowerSeries.coeff k ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) ≠ 0 →
        k ≤ Finsupp.single x n := by sorry
