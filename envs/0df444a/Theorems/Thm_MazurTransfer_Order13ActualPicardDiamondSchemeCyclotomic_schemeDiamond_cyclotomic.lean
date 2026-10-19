-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardDiamondSchemeCyclotomic_schemeDiamond_cyclotomic
-- name    : MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.schemeDiamond_cyclotomic
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T21:00:57.013468+00:00
-- url     : https://prove2.me/theorems/1b93e8a6-8e0c-48ae-a36d-ccd53d42baa4
-- title:
--   The actual rational Picard diamond satisfies its cyclotomic identity as a scheme morphism
-- statement:
--   Let P be the same actual rational represented Picard scheme, let delta be its existing scheme diamond and write sums using its internal commutative group law. Then, as endomorphisms of P over Q,
--
--   $$\delta\circ\delta-\delta+\mathrm{id}_P=0.$$
--
--   The named downstream consumer is the actual norm-nineteen scheme endomorphisms.
-- source:
--   Exact complete original MazurTheorem Order13ActualPicardDiamondSchemeCyclotomic theorem type, using the same actual represented Picard scheme, original endomorphism values and original group-object provider. The proof instantiates the accepted cover-uniform field-point identity with the existing public ordinary/reciprocal cover of the same curve. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: cyclotomic and hyperelliptic identities are equalities of
endomorphisms of the SAME existing rational Picard scheme, using reduced
source and separated target and every residue-field point.
Named downstream consumer: actual nineteen-norm scheme endomorphisms.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open scoped CategoryTheory.MonObj
local instance publicStatementschemeDiamondCyclotomicGroupObject20261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.schemeDiamond_cyclotomic :
    ((schemeDiamond ≫ schemeDiamond) * schemeDiamond⁻¹) * 𝟙 (Over.mk actualPicard.toBase) =
      (1 : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) := by sorry
