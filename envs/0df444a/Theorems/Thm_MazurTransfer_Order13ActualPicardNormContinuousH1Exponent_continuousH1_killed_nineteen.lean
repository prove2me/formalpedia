-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousH1Exponent_continuousH1_killed_nineteen
-- name    : MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.continuousH1_killed_nineteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T00:56:49.082391+00:00
-- url     : https://prove2.me/theorems/4bccd6d0-2696-4be2-924b-0611d1cabd76
-- title:
--   The continuous H1 of an actual exponent-nineteen norm kernel is killed by nineteen
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, and phi a finite internal group endomorphism. If every K-valued kernel element satisfies z to the nineteenth power equals one, then its presented continuous first-cohomology group satisfies $$\forall x\in H^1_{\mathrm{cont}}(\operatorname{Aut}_{\mathbb Q}(K),\ker(\varphi)(K)),\qquad 19x=0.$$ The canonical Krull topology and original discrete coefficient topology are retained. This supplies the original F19 module construction used in norm Selmer conditions. Finiteness and ranks remain separate claims.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousH1Exponent.continuousH1_killed_nineteen, complete original statement and original proof retained, Apache-2.0. A metadata-only comparison also checks the original point-topology constructor in full type and value.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels have exponent nineteen,
so their continuous H1 groups and rational norm quotients are killed by
nineteen. This does not assert finiteness. Named downstream consumer:
the finite-field structure and dimension bound in the actual Selmer group.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousH1ClassData
noncomputable section

open MazurTransfer
open MazurTransfer.Order13ActualPicardNormContinuousCocycles
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance publicNormContinuousH1ExponentStatementProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicNormContinuousH1ExponentStatementProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicNormContinuousH1ExponentStatementProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicNormContinuousH1ExponentStatementProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicNormContinuousH1ExponentStatementProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicNormContinuousH1ExponentStatementProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicNormContinuousH1ExponentStatementProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicNormContinuousH1ExponentStatementProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormContinuousCohomology

theorem MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.continuousH1_killed_nineteen (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] (h : ∀ z : Kernel K φ, z ^ 19 = 1)
    (x : ContinuousH1 K φ) : (19 : ℕ) • x = 0 := by sorry
