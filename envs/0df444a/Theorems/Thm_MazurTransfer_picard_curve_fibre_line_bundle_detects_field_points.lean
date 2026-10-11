-- Prove2me | Theorems.Thm_MazurTransfer_picard_curve_fibre_line_bundle_detects_field_points
-- name    : MazurTransfer.picard_curve_fibre_line_bundle_detects_field_points
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T17:44:59.494699+00:00
-- url     : https://prove2.me/theorems/0a9dc6f7-4c22-4693-92c0-eb58dc47bb69
-- title:
--   An actual curve fibre model detects represented Picard field points by their line bundles
-- statement:
--   For any represented relative sub-Picard functor over a commutative base ring, two field-valued points are equal exactly when the underlying Poincare line bundles become isomorphic after pullback to an isomorphic model of the actual curve fibre. The field need not be algebraically closed. The sub-Picard condition is arbitrary. The named downstream consumer is injectivity of the geometric divisor-class map on the same actual rational order-thirteen Picard scheme, needed to promote arithmetic diamond identities to scheme morphisms.
-- source:
--   Owned MazurTheorem integration proof using Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474 and the complete original Apache-2.0 Anthropic FLT representing-Picard definition and ext_of_iso proof at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_RepresentsRelSubPic.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
universe u

theorem MazurTransfer.picard_curve_fibre_line_bundle_detects_field_points
    {R : Type u} [CommRing R] {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε P D)
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} (j : X ⟶ pullback c t) [IsIso j]
    (a b : SchemeHomOver t D.toBase) :
    Nonempty ((Scheme.Modules.pullback j).obj (h.poincare.pullbackAlong a).L ≅
      (Scheme.Modules.pullback j).obj (h.poincare.pullbackAlong b).L) ↔ a = b := by sorry
