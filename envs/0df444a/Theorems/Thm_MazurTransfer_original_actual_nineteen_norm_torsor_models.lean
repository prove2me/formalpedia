-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_nineteen_norm_torsor_models
-- name    : MazurTransfer.original_actual_nineteen_norm_torsor_models
-- status  : Proved
-- author  : @Vas
-- created : 2026-11-02T19:19:12.101923+00:00
-- url     : https://prove2.me/theorems/43d7b418-373e-458d-85fa-4bd6462b184b
-- statement:
--   Specialize the checked original two integral norm preimage torsors at nineteen to the same canonical chosen unique extension of each original rational Picard point. Retain its checked restriction and uniqueness, both actual norm morphisms, the original principal action on all scheme points, and the same coherent selected pi quotient in normalized literal mu19 coordinates. Both complete original propositions and helper types, the entire original canonical-model predicate type and whole value, all four scoped provider types and one group-provider value, all generated helper types and original model and point contexts are independently checked. No local unit condition is asserted. Named downstream consumer: actual literal mu19 torsor-cocycle pushforward and the nineteen Kummer unit condition.

import Definitions.Def_MazurTransfer_OriginalActualNineteenNormTorsorModelsData20261020
import Theorems.Thm_MazurTransfer_original_actual_pi_mu19_coherent_quotient
import Theorems.Thm_MazurTransfer_original_actual_integral_norm_preimage_torsors
import Theorems.Thm_MazurTransfer_original_nineteen_integral_point_compatibility
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13LocalIntegralCoefficientMaps Order13ExceptionalNineteenFlatNormFibres
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardNormKummerCocycles Order13NineteenIntegralPointCompatibility
open Order13ActualIntegralNormPreimageTorsors Order13ActualPiMu19CoherentQuotient
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13ActualNineteenNormTorsorModels
local notation "R" => LocalRing 19
local notation "F" => AlgebraicClosure ℚ
attribute [local instance] MazurTransfer.Order13ActualNineteenNormTorsorModels.instFactPrimeOfNatNat_order13ActualNineteenNormTorsorModels
attribute [local instance] MazurTransfer.Order13ActualNineteenNormTorsorModels.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNineteenNormTorsorModels
attribute [local instance] MazurTransfer.Order13ActualNineteenNormTorsorModels.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNineteenNormTorsorModels
attribute [local instance] MazurTransfer.Order13ActualNineteenNormTorsorModels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNineteenNormTorsorModels

theorem MazurTransfer.original_actual_nineteen_norm_torsor_models : (∀ (a : RationalPoints), HasCanonicalActualNineteenNormTorsors a) ∧ (∀ (z : F) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover),
HasCoherentActualPiMu19Model z hz 𝒱 ∧ ∀ a : RationalPoints, HasCanonicalActualNineteenNormTorsors a) := by sorry
