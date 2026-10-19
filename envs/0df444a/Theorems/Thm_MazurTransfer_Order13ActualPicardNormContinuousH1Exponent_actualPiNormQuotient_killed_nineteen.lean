-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousH1Exponent_actualPiNormQuotient_killed_nineteen
-- name    : MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.actualPiNormQuotient_killed_nineteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T01:13:26.753999+00:00
-- url     : https://prove2.me/theorems/5265368c-5134-4221-ae2b-c8f450f9b5ad
-- title:
--   The actual pi rational norm quotient is killed by nineteen
-- statement:
--   For the same actual rational Picard P and the original pi norm map, every element of its rational norm quotient P(Q)/phi(P(Q)) has nineteenth power equal to one. This uses the accepted injective continuous Kummer group homomorphism and the original exponent-nineteen fact for the target continuous H1. It supplies the original module over F19 used in rational norm Selmer bounds. No finiteness, dimension bound or vanishing is asserted.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousH1Exponent.actualPiNormQuotient_killed_nineteen, Apache-2.0; original complete target and proof retained. Original group/topology/action provider full types and values are checked.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels have exponent nineteen,
so their continuous H1 groups and rational norm quotients are killed by
nineteen. This does not assert finiteness. Named downstream consumer:
the finite-field structure and dimension bound in the actual Selmer group.
-/
import Definitions.Def_MazurTransfer_Order13ActualSpecificContinuousNormH1ExponentData
noncomputable section
open MazurTransfer
open MazurTransfer.Order13ActualPicardNormContinuousH1Exponent
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance publicActualPiNormQuotientKilledNineteenStatementProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualPiNormQuotientKilledNineteenStatementProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicActualPiNormQuotientKilledNineteenStatementProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance publicActualPiNormQuotientKilledNineteenStatementProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormContinuousCocycles
local instance publicActualPiNormQuotientKilledNineteenStatementProvider1020261018 : IsGalois ℚ (AlgebraicClosure ℚ) := canonicalClosureGalois
open Order13ActualPicardNormContinuousKummerInjection
local instance publicActualPiNormQuotientKilledNineteenStatementProvider1120261018 : IsFinite schemePi.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1
local instance publicActualPiNormQuotientKilledNineteenStatementProvider1220261018 : IsFinite schemePiConjugate.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.1

theorem MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.actualPiNormQuotient_killed_nineteen (x : NormQuotient schemePi) : x ^ 19 = 1 := by sorry
