-- Prove2me | Theorems.Thm_MazurTransfer_original_selected_pi_mu19_quotient
-- name    : MazurTransfer.original_selected_pi_mu19_quotient
-- status  : Proved
-- author  : @Vas
-- created : 2026-11-02T16:31:57.785673+00:00
-- url     : https://prove2.me/theorems/980dad23-f61a-4b8e-98e0-9d0834e9672a
-- statement:
--   The checked normalized classification applies to the same finite flat quotient Hopf model and its same arithmetic root label. Freeness follows over the original local ring. Retain the original model, inclusion, injectivity, addition, Galois formula and selected pi restriction identity unchanged. The original scalar-change restriction square then identifies its literal mu19 quotient point with the previously selected piQuotient on the same original kernel label. Both complete original propositions and helper types, the whole original selected-model predicate, all twelve scoped provider types and four nonproof provider values, every generated helper type and all original chosen-map and point-operation contexts are independently checked. Named downstream consumer: pushforward of the actual integral pi norm-preimage torsor and its literal mu19 Kummer unit condition.

import Definitions.Def_MazurTransfer_OriginalSelectedPiMu19QuotientData20261020
import Theorems.Thm_MazurTransfer_original_rational_subring_mu19_classification
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SameIntegralPicardRationalSchemeComparison Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13IntegralRepresentationQuotient Order13ActualOrderedCharacterContinuousH1
open Order13RationalSubringBaseChange NineteenRootsGaloisRepresentation
open Order13RationalSubringMu19Classification CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points
open BialgebraBaseChangePointRestriction
open scoped CategoryTheory.MonObj TensorProduct
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
open MazurTransfer.Order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsMonHomOverSchemeSpecOfRatSchemePi_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instFactPrimeOfNatNat_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsFiniteLeftSchemeSchemePi_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsGaloisRatAlgebraicClosure_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instFactForallEqSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePiHPowOfNat_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instModuleZModOfNatNatAdditiveSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePi_order13SelectedPiMu19Quotient

theorem MazurTransfer.original_selected_pi_mu19_quotient : (∀ (G : Type) [CommRing G] [HopfAlgebra R G], ∀ {H : Type} [CommRing H] [HopfAlgebra R H]
    (j : H →ₐc[R] G) (f : WithConv (S ⊗[R] G →ₐ[S] F)),
fixedBasePoint H (BialgebraPointRestriction.restrictPoint (baseChangeMap («S» := S) j) f) =
      BialgebraPointRestriction.restrictPoint j (fixedBasePoint G f)) ∧ (∀ (z : F) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (G : Type) [CommRing G] [HopfAlgebra R G] (e : WithConv (G →ₐ[R] F) ≃ Additive (Kernel F schemePi)), ∀ (hQ : HasQuotientOfModel 19 F schemePi (rootsRepresentation F)
      (piQuotient F z hz 𝒱) G e),
HasSelectedNormalizedMu19Quotient z hz 𝒱 G e) := by sorry
