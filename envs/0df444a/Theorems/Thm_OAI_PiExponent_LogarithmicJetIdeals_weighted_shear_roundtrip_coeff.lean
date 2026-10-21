-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_roundtrip_coeff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_roundtrip_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T22:34:24.189993+00:00
-- url     : https://prove2.me/theorems/0729a964-fc80-4a27-8a27-7ecc1c0554da
-- title:
--   Inverse shear recovers polynomial coefficients
-- statement:
--   For a polynomial, applying the inverse triangular substitution to its forward-sheared formal series recovers each original polynomial coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_roundtrip_coeff
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (a : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
        (MvPolynomial.aeval
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q)) =
    MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q := by sorry
