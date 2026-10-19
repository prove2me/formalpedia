-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualCharacterGoodPrimeKernelLifts_hasGoodPrimeCharacterKummerSequence_of_intertwiners
-- name    : MazurTransfer.Order13ActualCharacterGoodPrimeKernelLifts.hasGoodPrimeCharacterKummerSequence_of_intertwiners
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T01:33:11.035013+00:00
-- url     : https://prove2.me/theorems/5423a6fd-95dc-451a-a563-80b3ae280438
-- statement:
--   For the actual norm maps, an injective character-line inclusion and surjective quotient map with exact middle kernel induce a continuous character Kummer sequence whose quotient-kernel classes lift to character cohomology classes unramified on every genuine valuation inertia group outside two, thirteen and nineteen. All original hypotheses and four proof helper types are retained and checked.

import Definitions.Def_MazurTransfer_Order13ActualCharacterGoodPrimeKernelLiftsOriginalData20261019
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyTrivialTargetInjection_coefficientMap_injective
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelGoodPrimeInertia_kernel_inertia_fixed
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerKernelControl_normQuotient_image_zero_iff_character_lift
import Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_continuous_norm_class_unramified
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualCharacterGoodPrimeKernelLifts
attribute [local instance] actualCharacterGoodPrimeKernelLiftsOriginalProvider120261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider220261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider320261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider420261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider520261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider620261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider720261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider820261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider920261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1020261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1120261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1220261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1320261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1420261019

theorem MazurTransfer.Order13ActualCharacterGoodPrimeKernelLifts.hasGoodPrimeCharacterKummerSequence_of_intertwiners (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
    {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
    [AddCommGroup V] [Module (ZMod 19) V]
    (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
    (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
    (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
    (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    HasGoodPrimeCharacterKummerSequence K φ σ τ hsurj := by sorry
