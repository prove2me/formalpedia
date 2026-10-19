-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernelCocycle_continuous
-- name    : MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernelCocycle_continuous
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:41:04.220869+00:00
-- url     : https://prove2.me/theorems/90f05fb4-1924-4e04-a368-c600ade8a7c7
-- title:
--   The actual finite norm preimage kernel cocycle is continuous
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, and phi a finite internal group endomorphism. If b is a K-valued point above a rational point a, then the actual kernel-valued cocycle $$\sigma\longmapsto\sigma(b)b^{-1}$$ is continuous from the canonical Krull automorphism group to the discrete geometric kernel. This supplies the actual continuous norm Kummer class; local Selmer conditions remain separate.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousCocycles.kernelCocycle_continuous, retaining the original preimage-orbit continuity helper and complete context. Apache-2.0.

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
local instance publicKernelCocycleContinuousStatementProvider920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicKernelCocycleContinuousStatementProvider1020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicKernelCocycleContinuousStatementProvider1120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicKernelCocycleContinuousStatementProvider1220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicKernelCocycleContinuousStatementProvider1320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicKernelCocycleContinuousStatementProvider1420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicKernelCocycleContinuousStatementProvider1520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicKernelCocycleContinuousStatementProvider1620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

theorem MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernelCocycle_continuous (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) :
    Continuous (kernelCocycle K φ a b hb) := by sorry
