-- Prove2me | Theorems.Thm_MazurTransfer_PicardGeometricFieldPointLineBundleInjectivity_geometricPointLineBundle_iso_iff
-- name    : MazurTransfer.PicardGeometricFieldPointLineBundleInjectivity.geometricPointLineBundle_iso_iff
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:01:42.992116+00:00
-- url     : https://prove2.me/theorems/e26914ae-a580-4724-a665-9a26f1720e7b
-- title:
--   A geometric line bundle detects equality of represented Picard field points on an isomorphic fibre model
-- statement:
--   Let C over a commutative ring R have a represented relative degree-zero Picard, let K be a field, and let X be an isomorphic model of the actual fibre over Spec K. For K-valued Picard points a and b, their associated actual line bundles satisfy
--
--   $$L_a\simeq L_b\quad\Longleftrightarrow\quad a=b.$$
--
--   No algebraic-closure hypothesis is imposed on K. The result preserves the full original ring, field, representation, fibre and isomorphism hypotheses and supplies point detection for the arithmetic-class map of the same rational Picard family.
-- source:
--   Complete original MazurTheorem PicardGeometricFieldPointLineBundleInjectivity.geometricPointLineBundle_iso_iff, with the complete original inverse-pullback object-isomorphism constructor made explicit. Official Anthropic FLT relative Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: on an isomorphic model of the actual curve fibre, the
underlying line bundle detects equality of represented Picard field points.
Named downstream consumer: injectivity of the geometric arithmetic class
of the existing rational order-13 Picard scheme.
-/
import Definitions.Def_MazurTransfer_PicardCurvePullbackGeometricFieldLineBundleData


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer.PicardCurvePullbackGeometricFieldLineBundle
variable {R : Type u} [CommRing R] {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} (j : X ⟶ pullback c t) [IsIso j]

theorem MazurTransfer.PicardGeometricFieldPointLineBundleInjectivity.geometricPointLineBundle_iso_iff (a b : SchemeHomOver t D.toBase) :
    Nonempty (geometricPointLineBundle c ε D h t j a ≅
      geometricPointLineBundle c ε D h t j b) ↔ a = b := by sorry
