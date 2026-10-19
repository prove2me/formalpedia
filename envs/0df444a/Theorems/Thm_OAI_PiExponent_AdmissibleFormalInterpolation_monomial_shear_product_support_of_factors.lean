-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_product_support_of_factors
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support_of_factors
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:13:31.601971+00:00
-- url     : https://prove2.me/theorems/68cbf3e9-0125-4c43-ac32-751cf5e77c4c
-- title:
--   Successor-coordinate support bound for finite products
-- statement:
--   If each factor has a bounded exponent in its matching successor coordinate and is supported away from all other successor coordinates, then every nonzero coefficient of their product with a zeroth-coordinate monomial prefactor obeys those bounds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support_of_factors
    {m : ℕ} (n : ℕ) (b : Fin m → ℕ)
    (f : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (e : Fin (m + 1) →₀ ℕ)
    (hf : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d (f i) ≠ 0 → d i.succ ≤ b i)
    (hzero : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ, ∀ j : Fin m,
      j ≠ i → d j.succ ≠ 0 → MvPowerSeries.coeff d (f i) = 0)
    (hne : MvPowerSeries.coeff e
      (MvPowerSeries.X 0 ^ n * ∏ i : Fin m, f i) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ b i := by sorry
