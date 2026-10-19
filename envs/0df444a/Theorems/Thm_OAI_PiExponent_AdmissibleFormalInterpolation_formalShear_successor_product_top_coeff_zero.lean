-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_successor_product_top_coeff_zero
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff_zero
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T17:47:35.012176+00:00
-- url     : https://prove2.me/theorems/405a8348-1627-4a56-aee9-3c90a655d96a
-- title:
--   Top successor coefficient at zero zeroth exponent
-- statement:
--   Under the matching successor-coordinate exponents, the coefficient is one when the requested zeroth-coordinate exponent is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff_zero
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hzero : d 0 = 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ)) = 1 := by sorry
