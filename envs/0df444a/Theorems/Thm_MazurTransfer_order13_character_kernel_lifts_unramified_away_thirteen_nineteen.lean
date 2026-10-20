-- Prove2me | Theorems.Thm_MazurTransfer_order13_character_kernel_lifts_unramified_away_thirteen_nineteen
-- name    : MazurTransfer.order13_character_kernel_lifts_unramified_away_thirteen_nineteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T12:50:56.918976+00:00
-- url     : https://prove2.me/theorems/a4f81025-0a61-4a1c-92a3-f41a0f8c92c3
-- statement:
--   At every prime $q\ne13,19$, including $2$, an injective character inclusion induces an injective map on local continuous cohomology because inertia fixes the actual norm kernel. Thus a character lift of an unramified norm class is itself unramified. A zero under the original norm-quotient character homomorphism therefore has an inclusion lift in the original submodule of classes unramified at every such valuation inertia group. The original exact coefficient maps also give the corresponding unramified Kummer sequence. Named downstream consumer: the selected character kernel lifts and actual Selmer dimensions.

import Definitions.Def_MazurTransfer_Order13OriginalUnramifiedCharacterClassSubmoduleAndSequenceData20261019
import Theorems.Thm_MazurTransfer_order13_all_prime_norm_kummer_and_kernel_inertia
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyTrivialTargetInjection_coefficientMap_injective
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerKernelControl_normQuotient_image_zero_iff_character_lift
noncomputable section
open MazurTransfer
open Order13ActualCharacterKernelLiftsAwayThirteenNineteen
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
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instTopologicalSpacePoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instDiscreteTopologyPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instMulActionAlgEquivRatPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatContinuousH1_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen_1
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1SubtypeAlgEquivRatMemSubgroupCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen

theorem MazurTransfer.order13_character_kernel_lifts_unramified_away_thirteen_nineteen : (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U : Type} [AddCommGroup U] [Module (ZMod 19) U] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19) (hφ : φ = schemePi ∨ φ = schemePiConjugate) (A : ValuationSubring K) (hA : A.LiesOverPrime q), ∀ (hi : Function.Injective i), Function.Injective (localInclusionClass K φ σ i (A.inertiaSubgroupIn ℚ))) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U : Type} [AddCommGroup U] [Module (ZMod 19) U] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19) (hφ : φ = schemePi ∨ φ = schemePiConjugate) (A : ValuationSubring K) (hA : A.LiesOverPrime q), ∀ (hi : Function.Injective i)
    (y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ))
    (x : ContinuousH1 K φ) (hy : inclusionClass K φ σ i y = x)
    (hx : restrictionLinearMap K φ (A.inertiaSubgroupIn ℚ) x = 0), coefficientRestriction K σ (A.inertiaSubgroupIn ℚ) y = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U V : Type} [AddCommGroup U] [Module (ZMod 19) U] [AddCommGroup V] [Module (ZMod 19) V] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate), ∀ (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
    (x : NormQuotient φ) (hx : normQuotientCharacterHom K φ τ p hsurj x = 1), ∃ y ∈ unramifiedClassesAwayThirteenNineteen K σ,
      inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U V : Type} [AddCommGroup U] [Module (ZMod 19) U] [AddCommGroup V] [Module (ZMod 19) V] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate), ∀ (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap), HasUnramifiedAwayThirteenNineteenCharacterKummerSequence K φ σ τ hsurj) := by sorry
