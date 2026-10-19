-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormSubgroupRestrictionF19_restrictedH1_killed_nineteen
-- name    : MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.restrictedH1_killed_nineteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T00:56:31.220996+00:00
-- url     : https://prove2.me/theorems/105eb43f-1164-4169-ad84-6e3b4aae83cb
-- title:
--   Restriction of continuous H1 of an actual exponent-nineteen norm kernel is killed by nineteen
-- statement:
--   Let K be a characteristic-zero Galois extension of Q and phi a finite internal group endomorphism of the same actual rational Picard. For every subgroup S of Aut_Q(K), assume all K-valued kernel elements satisfy z^19=1. Then every class in the presented continuous first cohomology of S with coefficients in this norm kernel satisfies 19 x = 0. The canonical Krull topology, inherited subgroup topology and original discrete coefficient topology are retained. This supplies the restricted F19 module structure in local norm conditions. No finiteness, rank or arithmetic identification of S is asserted.
-- source:
--   Original MazurTheorem Order13ActualPicardNormSubgroupRestrictionF19.restrictedH1_killed_nineteen, Apache-2.0, complete original Galois and finiteness hypotheses and original proof retained. Full type and original group/topology/action provider values are compared independently.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels have exponent nineteen,
so their continuous H1 groups and rational norm quotients are killed by
nineteen. This does not assert finiteness. Named downstream consumer:
the finite-field structure and dimension bound in the actual Selmer group.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
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
local instance publicNormRestrictedContinuousH1ExponentStatementProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicNormRestrictedContinuousH1ExponentStatementProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicNormRestrictedContinuousH1ExponentStatementProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicNormRestrictedContinuousH1ExponentStatementProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicNormRestrictedContinuousH1ExponentStatementProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicNormRestrictedContinuousH1ExponentStatementProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicNormRestrictedContinuousH1ExponentStatementProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicNormRestrictedContinuousH1ExponentStatementProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormContinuousCohomology

open MazurTransfer.Order13ActualPicardNormSubgroupRestriction

theorem MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.restrictedH1_killed_nineteen (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsFinite φ.left] (S : Subgroup (K ≃ₐ[ℚ] K)) (h19 : ∀ z : Kernel K φ, z ^ 19 = 1)
    (x : localContinuousH1 K φ S) : (19 : ℕ) • x = 0 := by sorry
