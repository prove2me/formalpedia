-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_top_of_injective_coordinates
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_of_injective_coordinates
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:06:12.428633+00:00
-- url     : https://prove2.me/theorems/87552a1a-f33b-47af-9531-0236261d2cbc
-- title:
--   Top coefficient of constant shifts on injective coordinates
-- statement:
--   For an injective family of variables disjoint from a distinguished variable, the coefficient at the exponent that matches each factor’s exponent and is zero on every other coordinate is one, regardless of the constant shifts.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_of_injective_coordinates
    {σ : Type*} [DecidableEq σ] {m : ℕ}
    (v : Fin m → σ) (x0 : σ)
    (hv : Function.Injective v)
    (hdisj : ∀ i : Fin m, v i ≠ x0)
    (c : Fin m → ℂ) (e : Fin m → ℕ)
    (d : σ →₀ ℕ)
    (hbase : d x0 = 0)
    (hcoord : ∀ i : Fin m, d (v i) = e i)
    (hout : ∀ x : σ, x ≠ x0 → (∀ i : Fin m, v i ≠ x) → d x = 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X (v i) + MvPowerSeries.C (c i)) ^ (e i)) = 1 := by sorry
