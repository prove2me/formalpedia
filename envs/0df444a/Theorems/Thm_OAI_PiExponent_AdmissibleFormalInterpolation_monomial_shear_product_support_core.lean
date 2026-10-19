-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_product_support_core
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support_core
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:19:23.826097+00:00
-- url     : https://prove2.me/theorems/9d8fbfea-7500-4d54-b7ae-962fa6c982cc
-- title:
--   Successor-coordinate support bound for finite products
-- statement:
--   A nonzero coefficient of a finite product has, in each successor coordinate, an exponent bounded by the matching factor’s bound when the other factors have no support in that coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support_core
    {m : ℕ} (b : Fin m → ℕ)
    (f : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hf : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d (f i) ≠ 0 → d i.succ ≤ b i)
    (hzero : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ, ∀ j : Fin m,
      j ≠ i → d j.succ ≠ 0 → MvPowerSeries.coeff d (f i) = 0)
    (e : Fin (m + 1) →₀ ℕ)
    (hne : MvPowerSeries.coeff e (∏ i : Fin m, f i) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ b i := by sorry
