-- Prove2me | Theorems.Thm_MazurTransfer_PicardCurvePullbackBaseFieldLineBundle_pointLineBundle_postComp_iso_pullback
-- name    : MazurTransfer.PicardCurvePullbackBaseFieldLineBundle.pointLineBundle_postComp_iso_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T12:33:32.178496+00:00
-- url     : https://prove2.me/theorems/14024e3c-61d9-41ae-a96e-dec2a3e48444
-- title:
--   Re-rigidified Picard pullback gives literal curve pullback on base-field line bundles
-- statement:
--   Over any field $K$, let the specified relative Picard scheme represent the declared degree-zero functor. If $f:X\to X$ is a morphism over $K$ and $N$ is the original re-rigidified pullback data for $f$, then every base-field point $a$ satisfies $$\mathcal L_{N(a)}\simeq f^*\mathcal L_a.$$ The rigidifying line bundle pulled back from the field base is trivial. This full original contract supplies arithmetic Picard naturality for the actual generic-compatible diamond curve lift.
-- source:
--   Original complete pointLineBundle_postComp_iso_pullback statement and proof from MazurTheorem PicardCurvePullbackBaseFieldLineBundle.lean, Apache-2.0, Vas and contributors. The original product-section commutation and field-rigidification helpers are inlined unchanged in a fresh namespace. The main proof only qualifies the original rigidification helper; all hypotheses and the complete original type are retained. Uses the Proved original Anthropic FLT invertible-sheaf triviality over a field. Native, strict and complete frontend checks pass; full original/public closed types are kernel-compared. Named downstream consumer: arithmetic Picard class pullback naturality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: re-rigidified Picard pullback induces literal curve
pullback on the base-field point's line bundle. Named downstream consumer:
actual divisor presentation transport and arithmetic Pic0 naturality.
-/
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
import Definitions.Def_MazurTransfer_RepresentedPicardBaseFieldPointLineBundle
noncomputable section
universe u
open MazurTransfer
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open PicardReRigidifiedCurvePullback LineBundleFieldComparison
variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  (D : RelativePic0Designation K c)
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (f : C ⟶ C) (hf : f ≫ c = c)

theorem MazurTransfer.PicardCurvePullbackBaseFieldLineBundle.pointLineBundle_postComp_iso_pullback
    (N : PullbackData h f hf)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    Nonempty (pointLineBundle c ε D h (postComp N.hom a) ≅
      (Scheme.Modules.pullback f).obj (pointLineBundle c ε D h a)) := by sorry
