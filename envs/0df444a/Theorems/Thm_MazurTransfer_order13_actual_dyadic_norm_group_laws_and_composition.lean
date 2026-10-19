-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_norm_group_laws_and_composition
-- name    : MazurTransfer.order13_actual_dyadic_norm_group_laws_and_composition
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T10:01:29.541717+00:00
-- url     : https://prove2.me/theorems/55436679-a8a2-42f6-8bf0-13ce8fb5ae1d
-- statement:
--   Let $N_\phi$ be the original unique integral extension of an arithmetic endomorphism $\phi$. Extension preserves every composition and identity, and the group endomorphisms preserve zero and multiplication. For the two actual norm factors,
--
--   $$N_\pi\circ N_{\pi^{\ast}}=N_{\pi^{\ast}}\circ N_\pi=\widetilde{[19]}.$$
--
--   Here $\widetilde{[19]}$ denotes the original chosen integral extension of rational multiplication by nineteen. Its comparison with multiplication for the local relative law is the next theorem. Named downstream consumer: that scalar comparison and finite etale norm fibres at two. The full statement also retains the original generic law comparison and all nine original universal clauses.

import Definitions.Def_MazurTransfer_Order13DyadicOriginalIntegralNormGroupLawAndCompositionData20261019
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedPicardGeometry
open Order13DyadicMixedGenericNorms Order13DyadicMixedIntegralNormExtensions
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedGenericNormGroupLaws
open Order13DyadicMixedIntegralNormGroupLaws Order13DyadicMixedIntegralNormComposition
open scoped CategoryTheory.MonObj
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormGroupLaws.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormUnit.instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard_order13DyadicMixedGenericNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormUnit.instFactPrimeOfNatNat_order13DyadicMixedGenericNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericGroupIdentity.instFactPrimeOfNatNat_order13DyadicMixedGenericGroupIdentity
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedGenericNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormComposition.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormComposition
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormPointwiseUnit.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormPointwiseUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormPointwiseUnit.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormPointwiseUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormUnit.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedGenericNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.instFactPrimeOfNatNat_order13DyadicMixedGenericNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormUnit.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormUnit.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormGroupLaws.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormComposition.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormComposition

theorem MazurTransfer.order13_actual_dyadic_norm_group_laws_and_composition : (∀ {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (rationalPicard).toBase), (genericLocalLaw).mul t x y = (genericRepresentedLaw).mul t x y) ∧ (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (rationalPicard).toBase), NeronModelInfra.schemeHomOverComp ((genericLocalLaw).mul t x y)
      (genericNorm φ) =
    (genericLocalLaw).mul t
      (NeronModelInfra.schemeHomOverComp x (genericNorm φ))
      (NeronModelInfra.schemeHomOverComp y (genericNorm φ))) ∧ (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], NeronModelInfra.schemeHomOverComp ((dyadicLaw).one (𝟙 _))
      (integralNorm φ) = (dyadicLaw).one (𝟙 _)) ∧ (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (BaseRing)))
    (x y : SchemeHomOver t (dyadicPicard).toBase), NeronModelInfra.schemeHomOverComp ((dyadicLaw).mul t x y) (integralNorm φ) =
    (dyadicLaw).mul t
      (NeronModelInfra.schemeHomOverComp x (integralNorm φ))
      (NeronModelInfra.schemeHomOverComp y (integralNorm φ))) ∧ (∀ (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase), integralNorm (φ ≫ ψ) =
      schemeHomOverComp (integralNorm φ) (integralNorm ψ)) ∧ (integralNorm (𝟙 (Over.mk actualPicard.toBase)) =
      schemeHomOverId (dyadicPicard).toBase) ∧ (schemeHomOverComp (integralPi) (integralPiConjugate) =
      integralScalarNineteen) ∧ (schemeHomOverComp (integralPiConjugate) (integralPi) =
      integralScalarNineteen) ∧ (schemeHomOverComp (integralPi) (integralPiConjugate) =
      schemeHomOverComp (integralPiConjugate) (integralPi)) := by sorry
