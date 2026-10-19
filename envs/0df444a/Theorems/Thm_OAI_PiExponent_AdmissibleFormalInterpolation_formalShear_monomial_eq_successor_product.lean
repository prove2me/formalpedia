-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_eq_successor_product
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_eq_successor_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:27:50.942609+00:00
-- url     : https://prove2.me/theorems/ddb70501-0323-4080-9b36-19e1133f513a
-- title:
--   Shear of a monomial as a product of coordinate factors
-- statement:
--   Expanding the definition of the shear on a monomial gives the product of the zeroth-coordinate variable power and the sheared successor-coordinate powers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_eq_successor_product
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (a : Fin (m + 1) →₀ ℕ) :
    formalShear delta (MvPolynomial.monomial a 1) =
      (MvPowerSeries.X 0) ^ (a 0) *
        ∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ) := by sorry
