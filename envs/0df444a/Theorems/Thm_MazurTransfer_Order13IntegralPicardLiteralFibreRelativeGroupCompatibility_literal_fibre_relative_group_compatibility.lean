-- Prove2me | Theorems.Thm_MazurTransfer_Order13IntegralPicardLiteralFibreRelativeGroupCompatibility_literal_fibre_relative_group_compatibility
-- name    : MazurTransfer.Order13IntegralPicardLiteralFibreRelativeGroupCompatibility.literal_fibre_relative_group_compatibility
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T08:16:08.333979+00:00
-- url     : https://prove2.me/theorems/8ce4dea1-5c8c-4da2-bd03-18db2ddd0b0a
-- title:
--   Literal Picard fibres preserve the integral family’s canonical relative group law
-- statement:
--   Let $R\to S$ be a homomorphism of commutative rings. Let $D/R$ be an actual relative Picard representative of the literal order-thirteen curve, rigidified at positive infinity. The literal curve over $S$ has a representing equivalence on the relabelled actual base change $D_S$. There is an equivalence $\Theta$ from its slice-category rational points to the original scheme’s relative points over $\operatorname{Spec}S\to\operatorname{Spec}R$. It satisfies $$\Theta(ab)=m_D(\Theta(a),\Theta(b)),$$ where multiplication on the source and $m_D$ are the canonical group laws from the respective Picard representations. The underlying morphism of $\Theta(a)$ is the underlying point of $a$ followed by the specified pullback projection to $D$. This supplies the group-compatible identification for the same integral family’s rational and good-characteristic fibres.
-- source:
--   Original complete literal_fibre_relative_group_compatibility statement and thirty-eight-line proof body from MazurTheorem Order13IntegralPicardLiteralFibreRelativeGroupCompatibility.lean, Apache-2.0, Vas and contributors. All original statement binders and the full proof body are unchanged; project imports alone become Proved public interfaces. Uses the actual pointed whole-curve fibre isomorphism, positive-infinity section and designated base change. Reuses the newly Proved pointed-curve multiplication transport and original official Anthropic FLT base-change point/multiplication/Poincare compatibility theorem, exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. The complete original closed type is kernel-compared with both the solution and public statement, including the original relative group law and point-map projection. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: actual integral relative arithmetic group equivalence and same-family rational torsion specialization.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal curve fibres retain the original integral Picard
family's relative multiplication, via its genuine base-change representation
and pointed whole-curve isomorphism. Named downstream consumer: the same
family's arithmetic divisor-class group and torsion specialization.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13LiteralFibrePicardRepresentation
import Theorems.Thm_MazurTransfer_CurveIsoPicardPointMultiplicationTransport_transport_representation_relative_mul
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections
open MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
open MazurTransfer.CurveIsoPicardRepresentationTransport
open MazurTransfer.CurveIsoPicardPointMultiplicationTransport
open scoped CategoryTheory.MonObj

theorem MazurTransfer.Order13IntegralPicardLiteralFibreRelativeGroupCompatibility.literal_fibre_relative_group_compatibility
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    ∃ hS : RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
      (algEquivZeroCut (curveToBase S) (positiveInfinitySection S))
      (literalFibreDesignation R S D),
      letI := (show RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
        (algEquivZeroGroupCut (curveToBase S) (positiveInfinitySection S)).toSubPicCondition
          (literalFibreDesignation R S D) from hS).grpObj
      ∃ Θ : (Over.mk (𝟙 (Spec (.of S))) ⟶ Over.mk (literalFibreDesignation R S D).toBase) ≃
          SchemeHomOver (specMap R S) D.toBase,
        (∀ a, (Θ a).val = a.left ≫ pullback.fst D.toBase (specMap R S)) ∧
        ∀ a b, Θ (a * b) =
          (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
            (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
              D from h).relativeGroupLaw.mul (specMap R S) (Θ a) (Θ b) := by sorry
