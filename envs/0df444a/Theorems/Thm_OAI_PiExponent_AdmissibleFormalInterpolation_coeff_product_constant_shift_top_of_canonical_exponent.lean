-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_top_of_canonical_exponent
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_of_canonical_exponent
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T18:20:48.029369+00:00
-- url     : https://prove2.me/theorems/3df64b96-8f5e-4533-8c58-56a2fee37a43
-- title:
--   Top coefficient for a canonical coordinate exponent
-- statement:
--   The coefficient at the sum of the coordinate exponents in a product of constant-shifted variable powers is one, including when some exponents are zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_of_canonical_exponent
    {σ : Type*} [DecidableEq σ] {m : ℕ}
    (v : Fin m → σ) (c : Fin m → ℂ) (e : Fin m → ℕ) :
    MvPowerSeries.coeff (∑ i : Fin m, Finsupp.single (v i) (e i))
        (∏ i : Fin m,
          (MvPowerSeries.X (v i) + MvPowerSeries.C (c i)) ^ (e i)) = 1 := by sorry
