-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_shear_top_zero_specialize
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_shear_top_zero_specialize
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:55:22.883419+00:00
-- url     : https://prove2.me/theorems/e38a4843-2850-4ddc-b64e-6eb150982604
-- title:
--   Specialize lifted series at zero zeroth exponent
-- statement:
--   For a requested exponent with zero zeroth coordinate, replacing each lifted univariate series by its constant coefficient preserves the coefficient of the successor-coordinate product.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_shear_top_zero_specialize
    {m : ℕ} (f : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hzero : d 0 = 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (f i)) ^ (a i.succ)) =
      MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + MvPowerSeries.C ((f i).constantCoeff)) ^
            (a i.succ)) := by sorry
