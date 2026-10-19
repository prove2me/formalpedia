-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_continuous_norm_kummer_and_fixed_quotient_unramified
-- name    : MazurTransfer.order13_actual_dyadic_continuous_norm_kummer_and_fixed_quotient_unramified
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T11:21:39.686992+00:00
-- url     : https://prove2.me/theorems/fdee5535-ab5d-4c47-b03f-3b9899de1647
-- statement:
--   Let $P/\mathbf{Q}$ be the fixed original degree-zero Picard scheme, and let $\pi$ and $\pi^{\ast}$ be its two actual norm endomorphisms. For $\phi\in\{\pi,\pi^{\ast}\}$, let $Q_\phi=P(\mathbf{Q})/\phi P(\mathbf{Q})$ and let $\kappa_\phi$ be the original continuous Kummer injection into the first cohomology of its geometric norm kernel. If a valuation subring of $\overline{\mathbf{Q}}$ lies above $2$, with inertia subgroup $I$, then every $x\in Q_\phi$ satisfies
--
--   $$\operatorname{res}_I\bigl(\kappa_\phi(x)\bigr)=0.$$
--
--   The statement also retains the original general norm-lift inertia assertion and its continuous-class restriction form over every field and Galois extension allowed by the original hypotheses. These four complete clauses supply the dyadic local condition needed by the selected-character Selmer and rank arguments.

import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalFixedNormQuotientScopedProvidersData20261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_internal_norm_morphisms_and_inertia
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormSubgroupRestriction_restrictedClass_zero_iff_subgroup_invariant_preimage
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePi_geometricPoint_surjective
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePiConjugate_geometricPoint_surjective
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormAlgebraicKummerInjection Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormContinuousCohomology
open Order13LocalIntegralCoefficientMaps
open Order13DyadicMixedQuadraticCharts
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsGaloisRatAlgebraicClosure_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsFiniteLeftSchemeSchemePi_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instTopologicalSpacePoints_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instMulActionAlgEquivRatPoints_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instFactPrimeOfNatNat_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instDiscreteTopologyPoints_order13DyadicMixedUnramifiedKummer

theorem MazurTransfer.order13_actual_dyadic_continuous_norm_kummer_and_fixed_quotient_unramified : (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ), actionHom K σ b = b) ∧ (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsGalois ℚ K] [IsFinite φ.left], ∀ (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a), restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0) ∧ (∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2)
    (x : NormQuotient schemePi), restrictNormClass (AlgebraicClosure ℚ) schemePi (A.inertiaSubgroupIn ℚ)
      (actualPiAlgebraicClosureContinuousKummerGroupHom x).toAdd = 0) ∧ (∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2)
    (x : NormQuotient schemePiConjugate), restrictNormClass (AlgebraicClosure ℚ) schemePiConjugate (A.inertiaSubgroupIn ℚ)
      (actualPiConjugateAlgebraicClosureContinuousKummerGroupHom x).toAdd = 0) := by sorry
