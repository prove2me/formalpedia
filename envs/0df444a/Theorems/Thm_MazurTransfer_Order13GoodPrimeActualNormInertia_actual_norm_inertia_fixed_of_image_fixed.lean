-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeActualNormInertia_actual_norm_inertia_fixed_of_image_fixed
-- name    : MazurTransfer.Order13GoodPrimeActualNormInertia.actual_norm_inertia_fixed_of_image_fixed
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T06:20:55.834617+00:00
-- url     : https://prove2.me/theorems/a167c7c7-9888-46f6-b888-d8595c41c0d0
-- title:
--   Inertia fixes an actual norm preimage when it fixes its image at a good prime
-- statement:
--   At every prime q not dividing 104 and different from 19, for either actual rational Picard norm endomorphism, an inertia automorphism fixing the image of a point fixes that point. The statement retains the full original field, local-ring algebra and scalar-tower context.
-- source:
--   MazurTheorem Order13GoodPrimeActualNormInertia.actual_norm_inertia_fixed_of_image_fixed.

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

theorem MazurTransfer.Order13GoodPrimeActualNormInertia.actual_norm_inertia_fixed_of_image_fixed (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra (LocalRing q) Ω]
    [IsScalarTower (LocalRing q) ℚ Ω]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime q)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ.left =
      x.val ≫ φ.left) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by sorry
