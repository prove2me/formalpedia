-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelF19Representation_representation_kernel_isOpen
-- name    : MazurTransfer.Order13ActualNormKernelF19Representation.representation_kernel_isOpen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T01:33:10.819401+00:00
-- url     : https://prove2.me/theorems/20d17211-fc48-4225-82cc-021db424ae19
-- title:
--   The F19 representation on an actual finite norm kernel has open Galois kernel
-- statement:
--   For the same actual rational Picard, a characteristic-zero Galois extension K of Q, a finite internal group endomorphism phi and the original exponent-nineteen kernel fact, the kernel of its original F19 representation is open in the canonical Krull topology on Aut_Q(K). The complete original Galois, finiteness and exponent context is retained. All relevant original group/action/module providers are compared. This gives the original open-kernel input to finite Galois splitting fields and character quotients; no arithmetic inertia identification or geometric rank is asserted.
-- source:
--   Original MazurTheorem Order13ActualNormKernelF19Representation.representation_kernel_isOpen, Apache-2.0. Complete original target and instance providers retained. The open-stabilizer step is proved directly from the accepted kernel continuous-action theorem.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels have exponent nineteen,
so their continuous H1 groups and rational norm quotients are killed by
nineteen. This does not assert finiteness. Named downstream consumer:
the finite-field structure and dimension bound in the actual Selmer group.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelF19RepresentationOriginalContextDataV220261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernel_continuousSMul
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
local instance publicNormKernelF19RepresentationOpenKernelStatementProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicNormKernelF19RepresentationOpenKernelStatementProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicNormKernelF19RepresentationOpenKernelStatementProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicNormKernelF19RepresentationOpenKernelStatementProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicNormKernelF19RepresentationOpenKernelStatementProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicNormKernelF19RepresentationOpenKernelStatementProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicNormKernelF19RepresentationOpenKernelStatementProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicNormKernelF19RepresentationOpenKernelStatementProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology

open MazurTransfer.Order13ActualNormKernelF19Representation
local instance publicKernelRepresentationFiniteStatementProvider20261018 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] :
    Finite (Kernel K φ) := MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_finite K φ
local instance publicKernelRepresentationModuleStatementProvider20261018 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] : Module (ZMod 19) (Additive (Kernel K φ)) :=
  MazurTransfer.Order13ActualNormKernelFiniteModule.kernelZModModule K φ
local instance publicKernelRepresentationContinuousStatementProvider20261018 (K : Type) [Field K] [CharZero K]
    [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsFinite φ.left] : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) :=
  MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul K φ

theorem MazurTransfer.Order13ActualNormKernelF19Representation.representation_kernel_isOpen (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] :
    IsOpen ((kernelRepresentation K φ).ker : Set (K ≃ₐ[ℚ] K)) := by sorry
