-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_continuous_norm_class_unramified
-- name    : MazurTransfer.Order13GoodPrimeUnramifiedKummer.continuous_norm_class_unramified
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T06:43:35.727611+00:00
-- url     : https://prove2.me/theorems/88fe8d1f-c295-4e4d-83a8-b7c21e757382
-- title:
--   Actual continuous norm Kummer classes are unramified at good primes
-- statement:
--   For every prime q not dividing 104 and different from 19, the actual continuous norm Kummer class of a rational Picard point restricts to zero on the valuation inertia subgroup for either actual norm endomorphism. The complete original Galois field and finite norm hypotheses are retained.
-- source:
--   MazurTheorem Order13GoodPrimeUnramifiedKummer.continuous_norm_class_unramified.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous Kummer classes for the SAME actual rational
norm maps restrict to zero on the genuine valuation inertia groups at
every prime outside two, thirteen and nineteen.
Named downstream consumer: global norm Selmer bounds.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13LocalIntegralCoefficientMaps
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
attribute [local instance] MazurTransfer.Order13ActualPicardNormKummerCocycles.actualPicardNormKummerDataProvider220261017

open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormSubgroupRestriction
attribute [local instance] MazurTransfer.Order13ActualPicardNormSubgroupRestriction.actualNormSubgroupRestrictionDataProvider520261018
attribute [local instance] MazurTransfer.Order13ActualPicardNormSubgroupRestriction.actualNormSubgroupRestrictionDataProvider620261018
attribute [local instance] MazurTransfer.Order13ActualPicardNormSubgroupRestriction.actualNormSubgroupRestrictionDataProvider720261018
attribute [local instance] MazurTransfer.Order13ActualPicardNormSubgroupRestriction.actualNormSubgroupRestrictionDataProvider820261018
attribute [local instance] MazurTransfer.Order13ActualPicardNormSubgroupRestriction.actualNormSubgroupRestrictionDataProvider920261018

local instance goodPrimeContinuousNormOriginalOrderKernelSmulPublicContext20261018
    (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsGalois ℚ K] [IsFinite φ.left] :
    ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ

theorem MazurTransfer.Order13GoodPrimeUnramifiedKummer.continuous_norm_class_unramified (q : ℕ) [Fact q.Prime]
    (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsGalois ℚ K] [IsFinite φ.left] (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    restrictNormClass K φ (A.inertiaSubgroupIn ℚ) (continuousClassOfLift K φ a b hb) = 0 := by sorry
