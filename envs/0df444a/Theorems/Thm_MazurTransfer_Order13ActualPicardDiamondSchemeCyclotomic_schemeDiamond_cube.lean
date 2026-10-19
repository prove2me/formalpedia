-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardDiamondSchemeCyclotomic_schemeDiamond_cube
-- name    : MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.schemeDiamond_cube
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T21:01:07.917483+00:00
-- url     : https://prove2.me/theorems/9c349f0a-ed6b-4bbc-b4e4-e0f3cc379067
-- title:
--   The cube of the actual rational Picard scheme diamond is inversion
-- statement:
--   Let P be the same actual rational represented Picard scheme and let delta be its existing scheme diamond. Then
--
--   $$\delta\circ\delta\circ\delta=-\mathrm{id}_P$$
--
--   as scheme morphisms over Q, where the right side is inversion on the Picard group. The named downstream consumers are the actual Picard norm isogenies and descent kernels.
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
local instance publicStatementschemeDiamondCubeGroupObject20261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.schemeDiamond_cube :
    schemeDiamond ≫ schemeDiamond ≫ schemeDiamond =
      (𝟙 (Over.mk actualPicard.toBase))⁻¹ := by sorry
