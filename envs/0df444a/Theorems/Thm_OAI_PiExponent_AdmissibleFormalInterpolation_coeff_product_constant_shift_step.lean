-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_step
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:45:39.793607+00:00
-- url     : https://prove2.me/theorems/00f6a450-5683-4720-9c54-80ca05da4b7a
-- title:
--   Top coefficient after one constant-shifted coordinate
-- statement:
--   If all coefficients of `φ` in total degrees above `k` vanish and its pure `x` coefficient at degree `k` is one, multiplying by `X x + C c` gives pure `x` coefficient one at degree `k + 1`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_step
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (k : ℕ) (φ : MvPowerSeries σ R) (c : R)
    (hbound : ∀ n : σ →₀ ℕ, k < n.sum (fun _ m => m) → MvPowerSeries.coeff n φ = 0)
    (htop : MvPowerSeries.coeff (Finsupp.single x k) φ = 1) :
    MvPowerSeries.coeff (Finsupp.single x (k + 1))
      (φ * (MvPowerSeries.X x + MvPowerSeries.C c)) = 1 := by sorry
