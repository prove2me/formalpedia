-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGaloisFixedPointDescent_fixed_point_descends
-- name    : MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.fixed_point_descends
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:18:16.923726+00:00
-- url     : https://prove2.me/theorems/4cc8410f-cb2b-41a4-8f9b-472677f2d574
-- title:
--   Every Galois-fixed geometric point of the actual Picard descends uniquely to a rational point
-- statement:
--   Let P be the same actual rational represented Picard group scheme and K a Galois extension of Q of characteristic zero. A K-point b fixed by every Q-automorphism has a unique rational descent: $$\bigl(\forall\sigma\in\operatorname{Aut}_{\mathbb Q}(K),\ \sigma(b)=b\bigr)\quad\Longrightarrow\quad\exists!a\in P(\mathbb Q),\ a_K=b.$$ The scalar-extension map and field-automorphism action are the original actual Picard constructors. The named downstream consumers are the rational-to-fixed group equivalence and the algebraic norm Kummer zero-class criterion.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGaloisFixedPointDescent.fixed_point_descends statement and main proof. Same actual represented Picard, original point/action/scalar-extension constructors and group provider, with complete original final type and provider values compared independently. Applies the accepted original unique over-point descent theorem with its original binder order. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

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
local instance publicActualPicardGaloisFixedPointDescentStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualPicardGaloisFixedPointDescentStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicActualPicardGaloisFixedPointDescentStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicActualPicardGaloisFixedPointDescentStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardGaloisFixedPointDescent

theorem MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.fixed_point_descends (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (b : Points K)
    (hb : ∀ σ : K ≃ₐ[ℚ] K, actionHom K σ b = b) :
    ∃! a : RationalPoints, rationalPoint K a = b := by sorry
