-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_top_coefficient
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_coefficient
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:36:26.749085+00:00
-- url     : https://prove2.me/theorems/64a3d94f-3092-433d-b16a-08768b763fe2
-- title:
--   Top coefficient of a finite product of constant-shifted coordinates
-- statement:
--   For any finite family of factors of the form `X x + C (a i)`, the coefficient at the exponent whose `x`-degree is the number of factors is one, regardless of the constants.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_coefficient
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (s : Finset ℕ) (a : ℕ → R) :
    MvPowerSeries.coeff (Finsupp.single x s.card)
        (∏ i ∈ s, (MvPowerSeries.X x + MvPowerSeries.C (a i))) = 1 := by sorry
