-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardDiamondFieldPointPullback_actualDiamondHom_field_point_pullback
-- name    : MazurTransfer.Order13ActualPicardDiamondFieldPointPullback.actualDiamondHom_field_point_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T11:44:29.000226+00:00
-- url     : https://prove2.me/theorems/337f36e4-70e2-4004-b590-7f0250ec2ca9
-- title:
--   The actual Picard diamond action pulls back line bundles by the inverse curve automorphism
-- statement:
--   For every field-valued point $a$ of the actual rational Picard scheme, the line bundle classified by its image under the specified diamond scheme endomorphism is isomorphic to the inverse-curve pullback of the line bundle classified by $a$: $$\mathcal L_{\Delta(a)}\simeq (\delta^{-1})^*\mathcal L_a.$$ The field can be any field equipped with the specified map to the rational base. The rigidifying correction is trivial over a field. This identifies the actual scheme action on field points for arithmetic Picard comparison.
-- source:
--   Original complete statement and main proof body from MazurTheorem Order13ActualPicardDiamondFieldPointPullback.lean, Apache-2.0, Vas and contributors. The original short field-rigidification helper is inlined unchanged under a fresh namespace. Uses the original Proved Anthropic FLT field invertible-sheaf triviality theorem at pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Native, strict and complete frontend checks pass; full original and public closed types are kernel-compared. Named downstream consumer: arithmetic Pic0 diamond comparison.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the actual Picard action on every field point is inverse-curve pullback.
Named downstream consumer: arithmetic Pic0 naturality and norm descent. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualPicardDiamondSchemeEndomorphism
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualDiamondCurveAutomorphism Order13ActualPicardDiamondSchemeEndomorphism

theorem MazurTransfer.Order13ActualPicardDiamondFieldPointPullback.actualDiamondHom_field_point_pullback (K : Type) [Field K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
    (a : SchemeHomOver t actualPicard.toBase) :
    Nonempty ((actualRepresentation.poincare.pullbackAlong (postComp actualDiamondHom a)).L ≅
      (Scheme.Modules.pullback (curveChange diamondCurveIso.inv diamondCurveIso_inv_over t)).obj
        (actualRepresentation.poincare.pullbackAlong a).L) := by sorry
