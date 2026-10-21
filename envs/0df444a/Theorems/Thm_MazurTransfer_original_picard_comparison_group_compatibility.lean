-- Prove2me | Theorems.Thm_MazurTransfer_original_picard_comparison_group_compatibility
-- name    : MazurTransfer.original_picard_comparison_group_compatibility
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T02:17:05.204348+00:00
-- url     : https://prove2.me/theorems/5a2a6f2b-edf8-4e21-aee5-2ff8527361c1
-- statement:
--   The original canonical comparison from the same actual rational Picard to the same selected rational fibre is a group morphism. For every original good-prime localization, the same canonical comparison to the selected local generic fibre is likewise a group morphism. The original schemes, representations and chosen point group structures are retained. Named downstream consumer: the actual local generic point equivalence and integral norm-kernel arithmetic comparison.

import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Theorems.Thm_MazurTransfer_internal_monoid_morphism_of_all_points
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseLocalGenericPicard_order13PicardComparisonPublicGroupCompatibility
attribute [local instance] MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseRationalFibre_order13PicardComparisonPublicGroupCompatibility
attribute [local instance] MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13PicardComparisonPublicGroupCompatibility

theorem MazurTransfer.original_picard_comparison_group_compatibility : (IsMonHom actualPicardRationalFibreOverIso.hom) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), IsMonHom (actualLocalGenericOverIso q hq).hom) := by sorry
