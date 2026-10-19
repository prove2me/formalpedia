-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeActualNormInertia_actual_norm_lift_of_rational_point_inertia_fixed
-- name    : MazurTransfer.Order13GoodPrimeActualNormInertia.actual_norm_lift_of_rational_point_inertia_fixed
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T06:28:17.614979+00:00
-- url     : https://prove2.me/theorems/df7dee33-96a7-4bdd-b8cb-bf84b945dbc6
-- title:
--   Inertia fixes an actual norm lift of a rational point at a good prime
-- statement:
--   For every prime outside 2,13,19 and either actual rational Picard norm map, every lift of a rational point is fixed by the inertia group of a valuation subring over that prime. The original field, local-ring algebra and scalar-tower contexts are retained in full.
-- source:
--   MazurTheorem Order13GoodPrimeActualNormInertia.actual_norm_lift_of_rational_point_inertia_fixed.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inertia fixes every geometric norm lift of a rational
point for the SAME actual rational Picard norm maps at good primes.
Named downstream consumer: unramified local Kummer restrictions.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalGenericPicardComparison Order13GoodPrimeIntegralNormExtensions
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm

theorem MazurTransfer.Order13GoodPrimeActualNormInertia.actual_norm_lift_of_rational_point_inertia_fixed (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra (LocalRing q) Ω]
    [IsScalarTower (LocalRing q) ℚ Ω]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime q)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (p : Spec (CommRingCat.of ℚ) ⟶ actualPicard.P)
    (hx : x.val ≫ φ.left = Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)) ≫ p) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by sorry
