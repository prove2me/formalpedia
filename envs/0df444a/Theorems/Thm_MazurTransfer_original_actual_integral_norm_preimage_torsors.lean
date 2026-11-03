-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_integral_norm_preimage_torsors
-- name    : MazurTransfer.original_actual_integral_norm_preimage_torsors
-- status  : Proved
-- author  : @Vas
-- created : 2026-11-02T17:10:53.750225+00:00
-- url     : https://prove2.me/theorems/fb5472c7-e1be-4c53-91dd-266eeda652a4
-- statement:
--   Apply the checked finite flat preimage torsor theorem to both same actual integral norm extensions at every original good prime and every given local Picard section. Their checked finiteness, flatness, local finite presentation, surjectivity and all-scheme-point unit and multiplication identities supply the exact original hypotheses. Retain the original preimage fibre and its principal-action isomorphism on every test scheme. The complete original proposition and helper type, original torsor predicate type and whole value, three scoped provider types and one group-provider whole value, both private original-type preservation certificates, all generated helper types and every original torsor and coefficient context are independently checked. Named downstream consumer: the selected literal mu19 pi quotient torsor and its Kummer unit condition.

import Definitions.Def_MazurTransfer_OriginalActualIntegralNormPreimageTorsorsData20261020
import Theorems.Thm_MazurTransfer_original_integral_norms_finite_flat_all_good_primes
import Theorems.Thm_MazurTransfer_original_relative_finite_flat_norm_preimage_torsor
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralNormGroupLaws
open Order13GoodPrimeIntegralNormPointwiseUnit
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open RelativeFiniteFlatNormPreimageTorsor
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13ActualIntegralNormPreimageTorsors
attribute [local instance] MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralNormPreimageTorsors
attribute [local instance] MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralNormPreimageTorsors
attribute [local instance] MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralNormPreimageTorsors

theorem MazurTransfer.original_actual_integral_norm_preimage_torsors : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of (LocalRing q)))) (localPicard q hq).toBase),
HasIntegralNormPreimageTorsor q hq schemePi a ∧
      HasIntegralNormPreimageTorsor q hq schemePiConjugate a) := by sorry
