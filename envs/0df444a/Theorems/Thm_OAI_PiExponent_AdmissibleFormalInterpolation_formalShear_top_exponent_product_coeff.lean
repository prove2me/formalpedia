-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_top_exponent_product_coeff
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_top_exponent_product_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:54:22.969409+00:00
-- url     : https://prove2.me/theorems/6da88861-440c-4995-93da-72bc966a0605
-- title:
--   Top successor coefficient vanishes for univariate shear inputs
-- statement:
--   For any family of univariate power series, the product of the corresponding sheared successor-variable powers has zero coefficient whenever all requested successor exponents are maximal and the requested zeroth exponent is positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_top_exponent_product_coeff
    {m : ℕ} (f : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hpos : d 0 ≠ 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (f i)) ^ (a i.succ)) = 0 := by sorry
