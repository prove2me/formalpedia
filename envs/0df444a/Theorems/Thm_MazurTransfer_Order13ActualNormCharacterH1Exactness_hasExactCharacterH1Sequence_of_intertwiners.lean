-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormCharacterH1Exactness_hasExactCharacterH1Sequence_of_intertwiners
-- name    : MazurTransfer.Order13ActualNormCharacterH1Exactness.hasExactCharacterH1Sequence_of_intertwiners
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T02:28:03.44198+00:00
-- url     : https://prove2.me/theorems/aa0aec5a-8d17-461d-9cd0-d21ebb5f2f51
-- title:
--   Exact actual norm-character intertwiners give the original global and subgroup continuous H1 sequences
-- statement:
--   Retain the same actual rational Picard norm kernel, its original characteristic-zero Galois field, finite internal group endomorphism, exponent-nineteen fact and original F19 representation. Given an injective intertwiner i into this kernel representation and a surjective intertwiner p from it, whose underlying linear image and kernel coincide, the original predicate HasExactCharacterH1Sequence holds. This supplies continuous actions on both coefficient wrappers and image-equals-kernel identities at the middle existing continuous H1 globally and after restriction to every subgroup with its inherited topology. Every original hypothesis is retained. The original arithmetic character intertwiners are inputs here. Named downstream consumer: kernel control for actual norm Selmer images.
-- source:
--   Original MazurTheorem Order13ActualNormCharacterH1Exactness.hasExactCharacterH1Sequence_of_intertwiners, Apache-2.0. Complete original final type, four original proof-helper types, all seventeen original source instance types and eleven nonproof provider values are compared, including all seven module providers. Five statement-preamble providers are also compared. The included-coefficient stabilizer step is proved directly from the accepted continuous kernel action.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual norm-character representation sequence is exact
at the EXISTING continuous H1 globally and after restriction to every subgroup.
Named downstream consumer: kernel control for actual norm Selmer images.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1ExactSequenceData
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyExactSequence_range_eq_ker
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
local instance publicNormCharacterExactH1SequenceStatementProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicNormCharacterExactH1SequenceStatementProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicNormCharacterExactH1SequenceStatementProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicNormCharacterExactH1SequenceStatementProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicNormCharacterExactH1SequenceStatementProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicNormCharacterExactH1SequenceStatementProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicNormCharacterExactH1SequenceStatementProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicNormCharacterExactH1SequenceStatementProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology

open MazurTransfer.Order13ActualNormKernelF19Representation
local instance publicCharacterExactSequenceFiniteStatementProvider20261018 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] :
    Finite (Kernel K φ) := MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_finite K φ
local instance publicCharacterExactSequenceModuleStatementProvider20261018 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] : Module (ZMod 19) (Additive (Kernel K φ)) :=
  MazurTransfer.Order13ActualNormKernelFiniteModule.kernelZModModule K φ
local instance publicCharacterExactSequenceContinuousStatementProvider20261018 (K : Type) [Field K] [CharZero K]
    [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsFinite φ.left] : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) :=
  MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul K φ

open MazurTransfer.Order13ActualNormCharacterH1Exactness
open MazurTransfer.Order13ActualNormCharacterContinuousH1

theorem MazurTransfer.Order13ActualNormCharacterH1Exactness.hasExactCharacterH1Sequence_of_intertwiners (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
    {U V : Type} [AddCommGroup U] [Module (ZMod 19) U] [AddCommGroup V] [Module (ZMod 19) V]
    (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
    (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
    (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
    (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    HasExactCharacterH1Sequence K φ σ τ := by sorry
