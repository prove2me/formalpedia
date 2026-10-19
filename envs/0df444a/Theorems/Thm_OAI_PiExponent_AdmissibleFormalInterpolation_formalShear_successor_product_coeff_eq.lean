-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_successor_product_coeff_eq
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_coeff_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:28:37.226486+00:00
-- url     : https://prove2.me/theorems/e7895fc3-f3a8-4ea1-98e3-1869974c0f65
-- title:
--   Coefficient of the sheared successor-coordinate product at its top exponents
-- statement:
--   When every successor-coordinate exponent equals the corresponding factor’s exponent, the product’s coefficient is determined solely by the zeroth-coordinate power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_coeff_eq
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, a i.succ = e i.succ) :
    MvPowerSeries.coeff e
        ((MvPowerSeries.X 0) ^ (a 0) *
          ∏ i : Fin m,
            (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ)) =
      PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0)) := by sorry
