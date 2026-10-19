-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finitePacketShearMatrix_mulVec_packetMap_eq_truncatedFormalJet
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_mulVec_packetMap_eq_truncatedFormalJet
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T12:31:54.09842+00:00
-- url     : https://prove2.me/theorems/4cf6942a-f098-4c6f-a8c1-49d37af11d2f
-- title:
--   Finite packet shear products are coefficients of the truncated formal jet
-- statement:
--   Under the weak truncation bound, the finite packet shear applied to the full logarithmic packet coefficients equals the strict-row coefficient vector of the truncated formal jet.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_mulVec_packetMap_eq_truncatedFormalJet
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (P : WeightedPolynomial w0 w H) :
    (finitePacketShearMatrix K
        (strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H)
        (fun i => (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
          PowerSeries.log ℂ)).mulVecLin
        (packetMap K w0 v0 theta w H r P) =
      (fun rho : InterpolationMatrix.Row K v0 theta w H =>
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (truncatedFormalJet T (fun i => (rho.1.val : ℂ) * r i) P.val)) := by sorry
