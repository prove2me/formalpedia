-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_mvPowerSeries_coeff_pow_vanish_below_weight
-- name    : OAI.PiExponent.LogarithmicJetIdeals.mvPowerSeries_coeff_pow_vanish_below_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T10:49:33.575666+00:00
-- url     : https://prove2.me/theorems/d37bd5ce-f35c-4d0a-a4a0-d762a0fa8c50
-- title:
--   Powers preserve a scaled weighted coefficient lower bound
-- statement:
--   For positive variable weights, if all coefficients of a multivariate power series below weighted degree `rho` vanish, then the coefficients of its `n`th power below weighted degree `n * rho` vanish.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.mvPowerSeries_coeff_pow_vanish_below_weight
    {d : ℕ} (q : Fin d → ℝ) (rho : ℝ)
    (f : MvPowerSeries (Fin d) ℂ) (n : ℕ)
    (hq : ∀ j, 0 < q j)
    (hcoeff : ∀ a : Fin d → ℕ,
      (∑ j, q j * (a j : ℝ)) < rho →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm a) f = 0) :
    ∀ a : Fin d → ℕ,
      (∑ j, q j * (a j : ℝ)) < (n : ℝ) * rho →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm a) (f ^ n) = 0 := by sorry
