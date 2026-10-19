-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncatedFormalJet_row_sum
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.truncatedFormalJet_row_sum
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T12:41:09.568711+00:00
-- url     : https://prove2.me/theorems/6b50b5fe-aed5-4b1d-bf0c-5a811f8fca5a
-- title:
--   Row coefficients of the truncated formal jet as a finite matrix sum
-- statement:
--   For a fixed strict row, the coefficient of the truncated formal jet equals the finite sum over admissible polynomial columns of the truncated logarithmic matrix entry times the polynomial’s column coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.truncatedFormalJet_row_sum
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (P : WeightedPolynomial w0 w H)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.1)
        (truncatedFormalJet T (fun i => (rho.1.val : ℂ) * r i) P.val) =
      ∑ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T rho c *
          MvPolynomial.coeff (InterpolationMatrix.exponentVector c.1) P.val := by sorry
