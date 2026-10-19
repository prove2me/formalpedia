-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerUnramified_pushed_norm_class_unramified
-- name    : MazurTransfer.Order13ActualNormCharacterKummerUnramified.pushed_norm_class_unramified
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T06:57:42.876475+00:00
-- url     : https://prove2.me/theorems/25a33e37-9fb9-4643-8b3a-4d18fcb1211b
-- title:
--   Actual coefficient pushforwards of norm Kummer classes are unramified at good primes
-- statement:
--   The pushforward of an actual continuous norm Kummer class through the given coefficient intertwiner restricts to zero on every valuation inertia group at primes q not dividing 104 and different from 19. The complete original context and the given intertwiner are retained.
-- source:
--   MazurTheorem MazurTransfer.Order13ActualNormCharacterKummerUnramified.pushed_norm_class_unramified.

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

theorem MazurTransfer.Order13ActualNormCharacterKummerUnramified.pushed_norm_class_unramified (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
    {V : Type} [AddCommGroup V] [_root_.Module (ZMod 19) V]
    (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
    (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
    (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate) (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (mapClass K φ τ f (continuousClassOfLift K φ a b hb)) = 0 := by sorry
