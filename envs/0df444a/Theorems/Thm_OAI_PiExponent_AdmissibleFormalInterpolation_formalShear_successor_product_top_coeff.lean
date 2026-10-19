-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_successor_product_top_coeff
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T17:40:14.609989+00:00
-- url     : https://prove2.me/theorems/53673a04-a7f2-40c4-b366-d7aa4327be78
-- title:
--   Top successor coefficient of the sheared product
-- statement:
--   At the exponent matching each successor-coordinate power, the sheared product has coefficient one when its zeroth-coordinate exponent is zero, and zero otherwise.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ)) =
      if d 0 = 0 then 1 else 0 := by sorry
