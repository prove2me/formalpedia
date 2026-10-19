-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_norm_lift_inertia_fixed
-- name    : MazurTransfer.Order13GoodPrimeUnramifiedKummer.norm_lift_inertia_fixed
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T06:35:48.158525+00:00
-- url     : https://prove2.me/theorems/0c47a397-1724-442c-ac36-1f2b8b50096a
-- title:
--   Rational actual norm lifts are fixed by good-prime inertia
-- statement:
--   For every prime q not dividing 104 and different from 19, every lift b of a rational actual Picard point through either actual norm map is fixed by the given valuation inertia automorphism. The original field, characteristic-zero and IsMonHom context is retained, without adding a Galois or finite-norm hypothesis.
-- source:
--   MazurTheorem Order13GoodPrimeUnramifiedKummer.norm_lift_inertia_fixed.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous Kummer classes for the SAME actual rational
norm maps restrict to zero on the genuine valuation inertia groups at
every prime outside two, thirteen and nineteen.
Named downstream consumer: global norm Selmer bounds.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
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

theorem MazurTransfer.Order13GoodPrimeUnramifiedKummer.norm_lift_inertia_fixed (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    actionHom K σ b = b := by sorry
