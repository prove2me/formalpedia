-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernel_continuousSMul
-- name    : MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:46:06.665418+00:00
-- url     : https://prove2.me/theorems/cf6cf6e6-6268-4215-b8d4-034c42f0e3f8
-- title:
--   The actual finite norm kernel has a continuous Galois action
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, and phi a finite internal group endomorphism of P. Give its geometric kernel the topology induced from the discrete K-point space. The canonical action $$\operatorname{Aut}_{\mathbb Q}(K)\times\ker(\varphi)(K)\longrightarrow\ker(\varphi)(K)$$ is continuous for the Krull topology on the automorphism group. No algebraic closure or etaleness assumption is added. This is used by continuous norm cocycles and continuous first cohomology.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul, retaining original preimage and kernel open-stabilizer proof helpers and complete original context. Apache-2.0. The original point-action provider is given by its explicit constructor and compared definitionally.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual norm fibres give continuous cocycles for the
Krull topology and discrete geometric kernel topology. Named downstream
consumer: continuous Kummer classes and the local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormDiscretePointTopologyExplicitPointActionDataV320261017
import Theorems.Thm_MazurTransfer_FiniteRationalFibreGaloisOrbit_stabilizer_isOpen
import Theorems.Thm_MazurTransfer_DiscreteOrbitContinuityFromOpenStabilizer_continuous_orbit

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
local instance publicKernelContinuousSMulExplicitPointActionV2StatementProvider920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicKernelContinuousSMulExplicitPointActionV2StatementProvider1020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicKernelContinuousSMulExplicitPointActionV2StatementProvider1120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicKernelContinuousSMulExplicitPointActionV2StatementProvider1220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicKernelContinuousSMulExplicitPointActionV2StatementProvider1320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicKernelContinuousSMulExplicitPointActionV2StatementProvider1420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicKernelContinuousSMulExplicitPointActionV2StatementProvider1520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicKernelContinuousSMulExplicitPointActionV2StatementProvider1620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

theorem MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := by sorry
