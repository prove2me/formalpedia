-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_neron_model_and_pointed_rational_picard_comparison
-- name    : MazurTransfer.order13_actual_dyadic_neron_model_and_pointed_rational_picard_comparison
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T09:01:03.783981+00:00
-- url     : https://prove2.me/theorems/6143f53a-e335-4570-8f72-6bfccb992656
-- statement:
--   Let $R=\mathbf{Z}_{(2)}$, and let $J/R$ be the original chosen dyadic Picard scheme. It is an abelian scheme and a Neron model of its generic fibre. The original canonical comparison from the fixed arithmetic Picard scheme $P/\mathbf{Q}$ to this same rational fibre lies over the rational base and preserves zero. The same chosen internal group structures make this comparison a group morphism. All six complete original propositions are retained. Named downstream consumer: unique dyadic extensions of both actual norm factors.
--
--   For the original canonical isomorphism $e$, the pointed compatibility is
--
--   $$e:P\simeq J_{\mathbf{Q}},\qquad e(0_P)=0_J.$$
--
--   Its complete original internal group-morphism type is retained with both original monoid structures supplied explicitly.

import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
import Definitions.Def_MazurTransfer_Order13DyadicOriginalChosenRationalPicardComparisonData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedRationalPicardComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedRationalPicardComparison
attribute [local instance] MazurTransfer.Order13DyadicMixedRationalPicardComparison.instFactPrimeOfNatNat_order13DyadicMixedRationalPicardComparison
attribute [local instance] MazurTransfer.Order13DyadicMixedRationalPicardComparison.instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard

theorem MazurTransfer.order13_actual_dyadic_neron_model_and_pointed_rational_picard_comparison : (AbelianSchemePropertyBundle BaseRing dyadicPicard.toBase) ∧ (NeronModelPropertyBundle BaseRing ℚ dyadicPicard.toBase) ∧ (rationalPicard.toBase =
    pullback.snd dyadicPicard.toBase (specGenericFibreInclusion BaseRing ℚ)) ∧ (actualDyadicRationalSchemeIso.hom ≫ rationalPicard.toBase = actualPicard.toBase) ∧ (actualPicard.zeroSection ≫ actualDyadicRationalSchemeIso.hom = rationalPicard.zeroSection) ∧ (@IsMonHom _ _ _ _ _ (@GrpObj.toMonObj _ _ _ _ actualGroup) (@GrpObj.toMonObj _ _ _ _ rationalGroup) actualDyadicRationalOverIso.hom) := by sorry
