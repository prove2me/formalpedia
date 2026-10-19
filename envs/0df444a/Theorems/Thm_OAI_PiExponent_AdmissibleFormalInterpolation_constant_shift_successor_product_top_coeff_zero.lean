-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_constant_shift_successor_product_top_coeff_zero
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.constant_shift_successor_product_top_coeff_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:55:50.472131+00:00
-- url     : https://prove2.me/theorems/9f89872e-b1b3-4d25-bab1-4a7f8966d2dd
-- title:
--   Top coefficient for a product with constant shifts
-- statement:
--   For any constant shifts, matching every requested successor exponent to its factor exponent and requesting zeroth exponent zero gives coefficient one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.constant_shift_successor_product_top_coeff_zero
    {m : ℕ} (c : Fin m → ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hzero : d 0 = 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + MvPowerSeries.C (c i)) ^ (a i.succ)) = 1 := by sorry
