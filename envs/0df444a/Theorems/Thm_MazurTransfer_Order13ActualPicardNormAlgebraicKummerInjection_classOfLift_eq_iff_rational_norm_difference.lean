-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicKummerInjection_classOfLift_eq_iff_rational_norm_difference
-- name    : MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.classOfLift_eq_iff_rational_norm_difference
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:42:05.246985+00:00
-- url     : https://prove2.me/theorems/23471c84-ba69-4bcb-8d3f-5a95c2ffabcb
-- title:
--   Actual norm lift classes agree exactly when the rational points differ by a rational norm
-- statement:
--   Let P be the same actual rational Picard group scheme, K a Galois extension of Q of characteristic zero, and phi an internal group endomorphism. Let b,b prime be K-valued preimages of rational points a,a prime. For the original algebraic H1 lift classes, $$[c_b]=[c_{b\prime}]\quad\Longleftrightarrow\quad\exists c\in P(\mathbb Q),\ \varphi(c)=a(a\prime)^{-1}.$$ The named downstream consumers are independence of the chosen lift, the original rational norm quotient map and its Kummer injection.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormAlgebraicKummerInjection.classOfLift_eq_iff_rational_norm_difference statement and proof with its original Galois context. The complete original lift_div, cocycle_div and classOfLift_div helper types and bodies are retained. Same actual Picard and original H1 constructors, group law and action providers; original H1 dependency provider values are compared in full. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance publicActualNormH1EqualityStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualNormH1EqualityStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicActualNormH1EqualityStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicActualNormH1EqualityStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology

theorem MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.classOfLift_eq_iff_rational_norm_difference (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (a a' : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a') :
    classOfLift K φ a b hb = classOfLift K φ a' b' hb' ↔
      ∃ c : RationalPoints, c ≫ φ = a / a' := by sorry
