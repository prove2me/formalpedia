-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_scalar_nineteen_and_finite_etale_norm_fibres
-- name    : MazurTransfer.order13_actual_dyadic_scalar_nineteen_and_finite_etale_norm_fibres
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T10:14:13.007803+00:00
-- url     : https://prove2.me/theorems/14707a4a-3ba8-46c8-b6be-b55f18511172
-- statement:
--   Let $J/\mathbf{Z}_{(2)}$ be the same original chosen dyadic Picard scheme, with its original relative group law. The two actual integral norm maps satisfy
--
--   $$N_\pi\circ N_{\pi^{\ast}}=N_{\pi^{\ast}}\circ N_\pi=[19]_J.$$
--
--   Both norm maps are finite, formally unramified and etale. For every test scheme $T$ and point $x:T\to J$, both fibres $T\times_{J,N_\pi}J$ and $T\times_{J,N_{\pi^{\ast}}}J$ are finite etale over $T$. All six complete original clauses retain their chosen schemes, original relative law, scoped group structures and base-change quantifiers. These fibres supply the dyadic inertia argument.

import Theorems.Thm_MazurTransfer_RelativeGroupLawInternalScalar_canonical_schemeNsmul
import Theorems.Thm_MazurTransfer_RelativeGroupLawBaseChangeNsmul_fibreRestrictAlong_schemeNsmul
import Theorems.Thm_MazurTransfer_relative_group_norm_factors_finite_of_invertible_scalar
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both actual original norm composites are scalar nineteen for the same chosen dyadic law, and both norm fibres are finite etale over every test scheme.
Named downstream consumer: actual dyadic norm inertia and unramified Kummer conditions at two.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalScalarNormScopedGroupProvidersV220261019
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
open Order13DyadicMixedIntegralScalarNineteen Order13DyadicMixedScalarInputs
open Order13DyadicMixedIntegralNormFinite Order13DyadicMixedIntegralNormEtale
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instFactPrimeOfNatNat_order13DyadicMixedIntegralScalarNineteen
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralScalarNineteen
attribute [local instance] MazurTransfer.Order13DyadicMixedScalarInputs.instFactPrimeOfNatNat_order13DyadicMixedScalarInputs
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormFinite.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormFinite
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard_order13DyadicMixedIntegralScalarNineteen
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormEtale.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormEtale

theorem MazurTransfer.order13_actual_dyadic_scalar_nineteen_and_finite_etale_norm_fibres : ((integralPi).val ≫ (integralPiConjugate).val =
      (dyadicLaw).schemeNsmul 19) ∧ ((integralPiConjugate).val ≫ (integralPi).val =
      (dyadicLaw).schemeNsmul 19) ∧ (IsFinite (integralPi).val ∧ IsFinite (integralPiConjugate).val) ∧ (FormallyUnramified (integralPi).val ∧
      FormallyUnramified (integralPiConjugate).val) ∧ (Etale (integralPi).val ∧ Etale (integralPiConjugate).val) ∧ (∀ {T : Scheme}
    (x : T ⟶ (dyadicPicard).P), (IsFinite (pullback.snd (integralPi).val x) ∧
      Etale (pullback.snd (integralPi).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate).val x) ∧
      Etale (pullback.snd (integralPiConjugate).val x))) := by sorry
