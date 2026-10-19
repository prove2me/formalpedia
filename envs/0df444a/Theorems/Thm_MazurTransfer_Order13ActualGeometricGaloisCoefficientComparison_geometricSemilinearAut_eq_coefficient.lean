-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisCoefficientComparison_geometricSemilinearAut_eq_coefficient
-- name    : MazurTransfer.Order13ActualGeometricGaloisCoefficientComparison.geometricSemilinearAut_eq_coefficient
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:52:24.502191+00:00
-- url     : https://prove2.me/theorems/44983c2b-9ee7-46f8-b008-d35a057eacfc
-- title:
--   The actual geometric Galois semilinear lift equals its coefficient lift
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $\sigma\in\operatorname{Aut}_{\mathbb Q}(K)$. The geometric semilinear automorphism attached to the same actual curve Galois isomorphism equals the coordinate-defined coefficient lift:
--   \[g_\sigma=c_\sigma.\]
--   The equality identifies both function-field automorphisms and their base-field automorphisms, allowing coefficient reflection covariance to be used for the existing arithmetic Picard action.
-- source:
--   MazurTheorem Order13ActualGeometricGaloisCoefficientComparison.geometricSemilinearAut_eq_coefficient, preserving four complete original comparison helper propositions and the exact original closed root; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13GeometricGenericEmbeddingBaseChangeData
import Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphism_geometricSemilinearAut_generic
noncomputable section
open AlgebraicCurve MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism
open MazurTransfer.Order13ActualFunctionFieldCoefficientAction
attribute [local instance] MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricGaloisOriginalFactProvider20261018
  MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricGaloisOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualGeometricGaloisCoefficientComparison.geometricSemilinearAut_eq_coefficient (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) :
    geometricSemilinearAut K σ = coefficientSemilinearAut K σ.toRingEquiv := by sorry
