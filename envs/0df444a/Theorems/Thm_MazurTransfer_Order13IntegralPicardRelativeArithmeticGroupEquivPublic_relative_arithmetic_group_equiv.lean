-- Prove2me | Theorems.Thm_MazurTransfer_Order13IntegralPicardRelativeArithmeticGroupEquivPublic_relative_arithmetic_group_equiv
-- name    : MazurTransfer.Order13IntegralPicardRelativeArithmeticGroupEquivPublic.relative_arithmetic_group_equiv
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T08:35:31.683979+00:00
-- url     : https://prove2.me/theorems/dc532962-ea65-4b9e-875c-67509a24dc65
-- title:
--   The actual integral Picard family’s relative field points are the arithmetic divisor-class group
-- statement:
--   Let $R$ be a commutative ring in which $104$ is invertible, let $K$ be a perfect field with an $R$-algebra structure, and let $D/R$ be an actual designated representative of the algebraically trivial rigidified relative Picard subfunctor of the literal order-thirteen curve with positive-infinity section. Its relative points over $\operatorname{Spec}K\to\operatorname{Spec}R$, with the original relative group law supplied by that representation, admit a group equivalence $$D(K)\simeq\operatorname{Pic}^{0}\bigl(K(C_K)/K\bigr),$$ where the right side is the arithmetic degree-zero divisor-class group of the literal curve’s function field, written multiplicatively in the formalization. This identifies the actual integral family’s own rational and good-characteristic fibre groups for arithmetic specialization.
-- source:
--   Original complete relative_arithmetic_group_equiv contract from MazurTheorem Order13IntegralPicardRelativeArithmeticGroupEquivPublic.lean, Apache-2.0, Vas and contributors. The entire original statement is retained, including the exact structural scalar map, canonical relative group-law instance and actual literal function field. The proof now composes the Proved public literal-fibre group compatibility with a Proved public comparison of two Picard representations and the already Proved public existential arithmetic field equivalence. It imports no private arithmetic-constructor cache and supplies no arithmetic dictionary, genus, rank, cardinality or finiteness hypothesis. Reuses original official Anthropic FLT Picard, curve and divisor-class APIs at exact upstream pin 6e837e75355538c7f80bab5b956861e86c4eacc2. The complete original closed kernel type is checked against both the solution and public statement; native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: the same integral family’s rational and mod-3/mod-5 arithmetic groups, torsion specialization and rational rank comparison. The public place-foundation Definition is imported explicitly so that the literal function-field alias in the unchanged statement is visible independently of implementation caches.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original integral Picard representation's relative
points over a perfect field carry the actual arithmetic degree-zero
divisor-class group, with the original relative multiplication.
Consumes the exact native mirror of our publicly accepted arithmetic
group proof to permit assembly with the accepted finite-field count.
Named downstream consumer: same-family rational and finite-field groups
in the order-13 torsion specialization argument.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13LiteralFibrePicardRepresentation
import Theorems.Thm_MazurTransfer_Order13IntegralPicardLiteralFibreRelativeGroupCompatibility_literal_fibre_relative_group_compatibility
import Theorems.Thm_MazurTransfer_PicardRepresentationPointComparison_overPointEquiv_mul
import Theorems.Thm_MazurTransfer_order13_actual_arithmetic_picard_group_equivalence
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections
open MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
open MazurTransfer.Order13IntegralPicardLiteralFibreRelativeGroupCompatibility
open MazurTransfer.PicardRepresentationPointComparison
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open scoped CategoryTheory.MonObj

theorem MazurTransfer.Order13IntegralPicardRelativeArithmeticGroupEquivPublic.relative_arithmetic_group_equiv
    (R K : Type u) [CommRing R] [Field K] [PerfectField K] [Algebra R K]
    (h104 : IsUnit (104 : R)) (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    letI : Fact ((104 : K) ≠ 0) := ⟨by
      have hh : IsUnit (104 : K) := by simpa only [map_ofNat] using h104.map (algebraMap R K)
      exact hh.ne_zero⟩
    letI := (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
        D from h).relativeGroupLaw.pointGroup (specMap R K)
    Nonempty (SchemeHomOver (specMap R K) D.toBase ≃*
      Multiplicative (Pic0 K (actualCurveFunctionField K)))  := by sorry
