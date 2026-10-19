-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_product_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:36:51.701625+00:00
-- url     : https://prove2.me/theorems/de90f744-a8fe-4aa0-8e00-7b95e730aedb
-- title:
--   Successor-coordinate support bound for shifted monomial products
-- statement:
--   If every added series is supported only in coordinate zero, every nonzero coefficient of the shifted monomial product has successor-coordinate exponents bounded by the corresponding monomial exponents.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support
    {m : ℕ} (a e : Fin (m + 1) →₀ ℕ)
    (g : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hg : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ, ∀ j : Fin m,
      d j.succ ≠ 0 → MvPowerSeries.coeff d (g i) = 0)
    (hne : MvPowerSeries.coeff e
      (MvPowerSeries.X 0 ^ a 0 *
        ∏ i : Fin m, (MvPowerSeries.X i.succ + g i) ^ a i.succ) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ a i.succ := by sorry
