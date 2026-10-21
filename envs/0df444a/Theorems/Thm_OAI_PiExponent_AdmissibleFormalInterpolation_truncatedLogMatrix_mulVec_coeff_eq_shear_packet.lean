-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncatedLogMatrix_mulVec_coeff_eq_shear_packet
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.truncatedLogMatrix_mulVec_coeff_eq_shear_packet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T11:59:00.753381+00:00
-- url     : https://prove2.me/theorems/15323be8-b9db-44ae-916f-ea1e0b406528
-- title:
--   Truncated logarithmic coefficients factor through the packet shear
-- statement:
--   Let the column weights, row weights, and scale parameter be positive, and suppose every truncation order satisfies
--
--   $$w_i/\theta\le T_i v_0.$$
--
--   For any polynomial P whose supported monomials have column weight at most H, let c(P) be its coefficient vector on the column simplex. Let Eδ act on the strict row simplex, with δᵢ equal to the logarithm truncated strictly below degree Tᵢ minus the full formal logarithm. Then
--
--   $$M_Tc(P)=E_\delta\,\mathrm{packetMap}(P).$$
--
--   This identity relates polynomial matrix evaluation to formal packet coefficients. It allows equality in the truncation bound and imposes no positivity condition on H or restriction on the packet centers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.truncatedLogMatrix_mulVec_coeff_eq_shear_packet
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (P : WeightedPolynomial w0 w H) :
    (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c => MvPolynomial.coeff (InterpolationMatrix.exponentVector c.val) P.val) =
      (finitePacketShearMatrix K
        (strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H)
        (fun i => (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
          PowerSeries.log ℂ)).mulVecLin
        (packetMap K w0 v0 theta w H r P) := by sorry
