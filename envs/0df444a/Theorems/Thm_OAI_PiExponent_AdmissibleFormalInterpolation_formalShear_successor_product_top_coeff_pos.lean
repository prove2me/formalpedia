-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_successor_product_top_coeff_pos
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:48:00.3228+00:00
-- url     : https://prove2.me/theorems/ad37ef2b-9ac3-4a92-839b-f8236fc9f06d
-- title:
--   Top successor coefficient at positive zeroth exponent
-- statement:
--   Under the matching successor-coordinate exponents, the coefficient is zero when the requested zeroth-coordinate exponent is positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff_pos
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hpos : d 0 ≠ 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ)) = 0 := by sorry
