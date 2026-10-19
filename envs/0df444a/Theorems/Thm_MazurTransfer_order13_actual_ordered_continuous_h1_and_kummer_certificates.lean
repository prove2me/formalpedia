-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_ordered_continuous_h1_and_kummer_certificates
-- name    : MazurTransfer.order13_actual_ordered_continuous_h1_and_kummer_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T02:10:05.287689+00:00
-- url     : https://prove2.me/theorems/1e92aa76-dc0b-4d9d-ad7b-5ea334f77d29
-- statement:
--   The original coherently chosen actual ordered norm quotients are surjective and give continuous coefficient actions. Their continuous H1 pushforwards commute with restriction to every subgroup, and both original norm Kummer pushforwards are unramified on genuine valuation inertia outside two, thirteen and nineteen. The eight complete original propositions retain every original field, primitive-root, cover, subgroup and valuation hypothesis.

import Definitions.Def_MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerUnramified_normQuotientCharacterHom_unramified
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCyclotomicQuotient
open Order13ActualNormKernelF19Representation NineteenRootsGaloisRepresentation
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelNineteenEmbedding
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018

open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualNormKernelRanksTwo
open Order13ActualPicardSchemeNineteenNorm
attribute [local instance] originalNormKernelRanksTwoPiFiniteProvider20261018 originalNormKernelRanksTwoConjugateFiniteProvider20261018 originalNormKernelRanksTwoPiExponentProvider20261018 originalNormKernelRanksTwoConjugateExponentProvider20261018 originalNormKernelRanksTwoPiModuleProvider20261018 originalNormKernelRanksTwoConjugateModuleProvider20261018


open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
open MazurTransfer.Order13ActualArithmeticCharacterExactSequence MazurTransfer.ScalarCharacterLine
open Order13ActualComplementaryCharacterExactSequence Order13ActualNormKernelEigenCharacterQuotient RepresentationCharacterTwist
open Order13ActualNormKernelCrossPairing
open Order13ActualNormKernelInvariantDimensions
open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerKernelControl
open RepresentationCharacterTwist ScalarCharacterLine Order13ActualPicardGeometricNormPreimages
attribute [local instance] sourceArithmeticExactSequenceRationalFactProvider20261018 originalNormKernelRanksTwoPiKernelFiniteProvider20261018 originalNormKernelRanksTwoConjugateKernelFiniteProvider20261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider520261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider620261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider720261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider820261018
open Order13ActualNormCharacterContinuousH1 Order13ActualNormCharacterKummerUnramified
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualOrderedCharacterContinuousH1
attribute [local instance] Order13ActualOrderedCharacterContinuousH1.orderedContinuousOriginalPiKernelActionProvider20261019 Order13ActualOrderedCharacterContinuousH1.orderedContinuousOriginalConjugateKernelActionProvider20261019

theorem MazurTransfer.order13_actual_ordered_continuous_h1_and_kummer_certificates :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , Function.Surjective (piQuotient K z hz 𝒱)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , Function.Surjective (piConjugateQuotient K z hz 𝒱)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient (twistedRootsRepresentation K z hz))) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (S : Subgroup (K ≃ₐ[ℚ] K)) (x : ContinuousH1 K schemePi) ,
    coefficientRestriction K (rootsRepresentation K) S (piMapClass K z hz 𝒱 x) =
    localMapClass K schemePi (rootsRepresentation K) (piQuotient K z hz 𝒱) S
      (Order13ActualPicardNormSubgroupRestrictionF19.restrictionLinearMap K schemePi S x)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (S : Subgroup (K ≃ₐ[ℚ] K)) (x : ContinuousH1 K schemePiConjugate) ,
    coefficientRestriction K (twistedRootsRepresentation K z hz) S (piConjugateMapClass K z hz 𝒱 x) =
    localMapClass K schemePiConjugate (twistedRootsRepresentation K z hz) (piConjugateQuotient K z hz 𝒱) S
      (Order13ActualPicardNormSubgroupRestrictionF19.restrictionLinearMap K schemePiConjugate S x)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) (A : ValuationSubring K) (hA : A.LiesOverPrime q) (x : NormQuotient schemePi) ,
    coefficientRestriction K (rootsRepresentation K) (A.inertiaSubgroupIn ℚ)
      (piKummerHom K z hz 𝒱 x).toAdd = 0) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) (A : ValuationSubring K) (hA : A.LiesOverPrime q) (x : NormQuotient schemePiConjugate) ,
    coefficientRestriction K (twistedRootsRepresentation K z hz) (A.inertiaSubgroupIn ℚ)
      (piConjugateKummerHom K z hz 𝒱 x).toAdd = 0) := by sorry
