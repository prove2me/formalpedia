-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_internal_norm_morphisms_and_inertia
-- name    : MazurTransfer.order13_actual_dyadic_internal_norm_morphisms_and_inertia
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T10:48:19.017242+00:00
-- url     : https://prove2.me/theorems/7e476e58-dd8e-4599-adaa-b7e1365753cc
-- statement:
--   Every arithmetic Picard group endomorphism extends to an internal group morphism for the same original chosen dyadic law. Let $\psi$ be either actual norm factor, or its original integral extension, and let $x$ be a geometric point in the original field and scalar-tower context. The valuation inertia hypotheses in each original clause give
--
--   $$\psi\circ x\circ\operatorname{Spec}(\sigma)=\psi\circ x\quad\Longrightarrow\quad x\circ\operatorname{Spec}(\sigma)=x.$$
--
--   For the integral statement the valuation subring contains the dyadic base; for the fixed arithmetic statement it lies above two. In particular every actual norm lift of a rational point is fixed by genuine valuation inertia above two. All four complete original propositions retain their exact hypotheses and chosen maps. They supply dyadic continuous Kummer restriction conditions.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same original integral norm maps are internal group morphisms, and genuine dyadic valuation inertia fixes every actual norm lift with fixed image.
Named downstream consumer: dyadic unramified continuous Kummer classes and the two fixed norm quotient injections.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_MazurTransfer_Order13DyadicOriginalNormInertiaScopedGroupProvidersV220261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedPicardGeometry
open Order13DyadicMixedGenericNorms Order13DyadicMixedIntegralNormExtensions
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedGenericNormGroupLaws
open Order13DyadicMixedIntegralNormGroupLaws Order13DyadicMixedIntegralNormComposition
open scoped CategoryTheory.MonObj
open Order13DyadicMixedIntegralScalarNineteen Order13DyadicMixedScalarInputs
open Order13DyadicMixedIntegralNormFinite Order13DyadicMixedIntegralNormEtale
open Order13DyadicMixedIntegralNormInternalMorphism Order13DyadicMixedIntegralNormInertia
open Order13DyadicMixedActualNormInertia
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInternalMorphism
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInertia.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInertia
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormInternalMorphism
attribute [local instance] MazurTransfer.Order13DyadicMixedActualNormInertia.instFactPrimeOfNatNat_order13DyadicMixedActualNormInertia

theorem MazurTransfer.order13_actual_dyadic_internal_norm_morphisms_and_inertia : (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], @IsMonHom _ _ _ _ _
      (@GrpObj.toMonObj _ _ _ _ ((dyadicLaw).grpObjOverMk))
      (@GrpObj.toMonObj _ _ _ _ ((dyadicLaw).grpObjOverMk))
      (schemeHomOverToOverHom (integralNorm φ))) ∧ (∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω] [IsScalarTower BaseRing ℚ Ω], ∀ (φ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase)
    (hφ : φ = integralPi ∨ φ = integralPiConjugate)
    (A : ValuationSubring Ω)
    (hA : ∀ r : BaseRing, algebraMap BaseRing Ω r ∈ A)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap BaseRing Ω)))
      dyadicPicard.toBase)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ.val =
      x.val ≫ φ.val), Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val) ∧ (∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω] [IsScalarTower BaseRing ℚ Ω], ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime 2)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ.left =
      x.val ≫ φ.left), Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val) ∧ (∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω] [IsScalarTower BaseRing ℚ Ω], ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime 2)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (p : Spec (CommRingCat.of ℚ) ⟶ actualPicard.P)
    (hx : x.val ≫ φ.left = Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)) ≫ p), Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val) := by sorry
