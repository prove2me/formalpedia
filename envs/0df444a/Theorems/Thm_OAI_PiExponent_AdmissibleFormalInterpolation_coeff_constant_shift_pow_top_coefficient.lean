-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_constant_shift_pow_top_coefficient
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_top_coefficient
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:31:04.229482+00:00
-- url     : https://prove2.me/theorems/d8c09362-71f1-4760-98bc-6d5cd005f47d
-- title:
--   Top coefficient of a constant-shifted coordinate power
-- statement:
--   The coefficient at exponent `Finsupp.single x n` in the nth power of `X x + C a` is one, for every natural exponent including zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_top_coefficient
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (a : R) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single x n)
        ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) = 1 := by sorry
