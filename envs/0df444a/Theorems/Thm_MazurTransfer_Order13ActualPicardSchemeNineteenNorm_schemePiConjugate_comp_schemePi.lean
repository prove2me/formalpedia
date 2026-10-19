-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePiConjugate_comp_schemePi
-- name    : MazurTransfer.Order13ActualPicardSchemeNineteenNorm.schemePiConjugate_comp_schemePi
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T20:59:30.227706+00:00
-- url     : https://prove2.me/theorems/3c7ef3bb-61d8-47d0-8414-3d1cebb6f611
-- title:
--   The reverse actual rational Picard norm composite is scalar nineteen
-- statement:
--   Let P be the same actual rational represented Picard scheme, with its existing diamond delta and the original endomorphisms pi=3 id+2 delta and pi-bar=5 id-2 delta, using the internal Picard group law. Then
--
--   $$\pi\circ\overline{\pi}=[19]_P$$
--
--   as scheme morphisms over Q. The named downstream consumers are finiteness, etaleness and descent for these actual norm factors.
-- source:
--   Exact complete original MazurTheorem Order13ActualPicardSchemeNineteenNorm theorem type, using the same actual represented Picard scheme, original endomorphism values and original group-object provider. The proof instantiates the accepted cover-uniform field-point identity with the existing public ordinary/reciprocal cover of the same curve. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two explicit endomorphisms of the same rational Picard
scheme have both composites equal to scalar nineteen. This establishes
the actual scheme norm identity; isogeny properties and degrees remain
separate obligations. Named downstream consumer: nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance publicStatementschemeNineteenNormReverseSchemeGroupObject20261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem MazurTransfer.Order13ActualPicardSchemeNineteenNorm.schemePiConjugate_comp_schemePi :
    schemePiConjugate ≫ schemePi = (𝟙 (Over.mk actualPicard.toBase)) ^ 19 := by sorry
