-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCohomology_continuousClassOfLift_zero_iff_rational_preimage
-- name    : MazurTransfer.Order13ActualPicardNormContinuousCohomology.continuousClassOfLift_zero_iff_rational_preimage
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:58:39.568816+00:00
-- url     : https://prove2.me/theorems/edce7162-c2a8-42e9-a9b8-6e8f24291e20
-- title:
--   The actual continuous norm class vanishes exactly for rational norm preimages
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, and phi a finite internal group endomorphism. Let b be a K-valued preimage of a rational point a. The original continuous kernel cocycle class satisfies $$[b]_{\mathrm{cont}}=0\quad\Longleftrightarrow\quad\exists c\in P(\mathbb Q),\ \varphi(c)=a.$$ Thus vanishing of the continuous norm class detects rational norm divisibility. The original statement assumes the given geometric preimage, without requiring global geometric surjectivity or algebraic closure.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousCohomology complete declaration and original proof body, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual continuous kernel cocycles determine classes
in continuous H1, defined as continuous cocycles modulo coboundaries.
These classes have an injective forgetful map to Mathlib algebraic H1.
Named downstream consumer: actual continuous Kummer quotient injections.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousH1ClassData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicCohomology_classOfLift_zero_iff_rational_norm_preimage
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
local instance publicContinuousH1ZeroCriterionStatementProvider920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicContinuousH1ZeroCriterionStatementProvider1020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicContinuousH1ZeroCriterionStatementProvider1120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicContinuousH1ZeroCriterionStatementProvider1220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicContinuousH1ZeroCriterionStatementProvider1320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicContinuousH1ZeroCriterionStatementProvider1420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicContinuousH1ZeroCriterionStatementProvider1520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicContinuousH1ZeroCriterionStatementProvider1620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormContinuousCohomology

theorem MazurTransfer.Order13ActualPicardNormContinuousCohomology.continuousClassOfLift_zero_iff_rational_preimage (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) :
    continuousClassOfLift K φ a b hb = 0 ↔ ∃ c : RationalPoints, c ≫ φ = a := by sorry
