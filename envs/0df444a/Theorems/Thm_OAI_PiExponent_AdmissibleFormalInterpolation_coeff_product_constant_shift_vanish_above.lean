-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_vanish_above
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_vanish_above
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:45:32.021981+00:00
-- url     : https://prove2.me/theorems/93d596bb-c591-4cba-9867-a58206458eaf
-- title:
--   Degree bound for a product of constant-shifted coordinates
-- statement:
--   The product of `s.card` linear factors has zero coefficient at any exponent whose total degree exceeds `s.card`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_vanish_above
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (s : Finset ℕ) (a : ℕ → R) (n : σ →₀ ℕ)
    (h : s.card < n.sum (fun _ m => m)) :
    MvPowerSeries.coeff n
      (∏ i ∈ s, (MvPowerSeries.X x + MvPowerSeries.C (a i))) = 0 := by sorry
