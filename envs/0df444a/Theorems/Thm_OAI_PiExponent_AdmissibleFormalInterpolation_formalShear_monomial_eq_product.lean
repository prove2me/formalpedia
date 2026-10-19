-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_eq_product
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_eq_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:33:46.698376+00:00
-- url     : https://prove2.me/theorems/d40018ae-906d-4a2b-83de-0b1ee8945f8c
-- title:
--   Product formula for a sheared monomial
-- statement:
--   The shear of a monomial is the product of the zeroth coordinate power and the shifted successor-coordinate powers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_eq_product
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (a : Fin (m + 1) →₀ ℕ) :
    formalShear delta (MvPolynomial.monomial a 1) =
      MvPowerSeries.X 0 ^ a 0 *
        ∏ i : Fin m, (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ a i.succ := by sorry
