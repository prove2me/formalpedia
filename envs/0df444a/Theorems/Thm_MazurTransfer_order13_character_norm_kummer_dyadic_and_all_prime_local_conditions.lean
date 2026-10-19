-- Prove2me | Theorems.Thm_MazurTransfer_order13_character_norm_kummer_dyadic_and_all_prime_local_conditions
-- name    : MazurTransfer.order13_character_norm_kummer_dyadic_and_all_prime_local_conditions
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T12:06:36.808927+00:00
-- url     : https://prove2.me/theorems/6f971323-ffa4-4aae-9f58-82cce4bfcf93
-- statement:
--   Every continuous Kummer class for either actual norm map, pushed through any original character intertwiner, has zero restriction to genuine valuation inertia at $2$ and every prime $q\ne13,19$. The same holds for the original norm-quotient character homomorphism. All four original universal propositions retain their norm maps, chosen pushforward and quotient constructions, fields and topologies. Named downstream consumer: the two previously selected ordered character local conditions and actual Selmer bounds.

import Definitions.Def_MazurTransfer_Order13OriginalCharacterLocalConditionScopedTopologyAndModuleData20261019
import Theorems.Thm_MazurTransfer_order13_all_prime_norm_kummer_and_kernel_inertia
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation Order13ActualNormCharacterKummerUnramified
open Order13ActualNormCharacterContinuousH1 Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormContinuousCocycles Order13ActualPicardNormAlgebraicKummerInjection
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instTopologicalSpacePoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instDiscreteTopologyPoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instMulActionAlgEquivRatPoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatContinuousH1_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualNormCharacterDyadicKummerConditions

theorem MazurTransfer.order13_character_norm_kummer_dyadic_and_all_prime_local_conditions : (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate), ∀ (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a), coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (mapClass K φ τ f (continuousClassOfLift K φ a b hb)) = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hsurj : Function.Surjective (normHom K φ)) (hφ : φ = schemePi ∨ φ = schemePiConjugate), ∀ (A : ValuationSubring K) (hA : A.LiesOverPrime 2) (x : NormQuotient φ), coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (normQuotientCharacterHom K φ τ f hsurj x).toAdd = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate) (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19), ∀ (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a), coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (mapClass K φ τ f (continuousClassOfLift K φ a b hb)) = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hsurj : Function.Surjective (normHom K φ)) (hφ : φ = schemePi ∨ φ = schemePiConjugate) (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19), ∀ (A : ValuationSubring K) (hA : A.LiesOverPrime q) (x : NormQuotient φ), coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (normQuotientCharacterHom K φ τ f hsurj x).toAdd = 0) := by sorry
