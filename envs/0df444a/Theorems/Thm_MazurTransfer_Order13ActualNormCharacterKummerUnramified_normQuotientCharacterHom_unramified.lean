-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerUnramified_normQuotientCharacterHom_unramified
-- name    : MazurTransfer.Order13ActualNormCharacterKummerUnramified.normQuotientCharacterHom_unramified
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T07:09:20.185284+00:00
-- url     : https://prove2.me/theorems/80b7eb9c-7362-4d75-a059-0b5732dab097
-- title:
--   Actual norm quotient character homomorphisms are unramified at good primes
-- statement:
--   The character-valued actual norm quotient homomorphism restricts to zero on every valuation inertia group at primes q not dividing 104 and different from 19. The original surjectivity and coefficient-intertwiner inputs are retained.
-- source:
--   MazurTheorem MazurTransfer.Order13ActualNormCharacterKummerUnramified.normQuotientCharacterHom_unramified.

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerPushforwardData
noncomputable section
open MazurTransfer
open MazurTransfer.Order13ActualNormCharacterKummerUnramified
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider120261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider220261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider320261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider420261018

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider520261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider620261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider720261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider820261018



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider920261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider1020261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider1120261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterKummerUnramified.actualNormCharacterKummerPushforwardDataProvider1220261018

open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualNormCharacterContinuousH1

theorem MazurTransfer.Order13ActualNormCharacterKummerUnramified.normQuotientCharacterHom_unramified (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
    {V : Type} [AddCommGroup V] [_root_.Module (ZMod 19) V]
    (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
    (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
    (hsurj : Function.Surjective (normHom K φ))
    (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate) (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (x : NormQuotient φ) :
    coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (normQuotientCharacterHom K φ τ f hsurj x).toAdd = 0 := by sorry
