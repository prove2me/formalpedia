-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousKummerInjection_continuousQuotientHom_injective
-- name    : MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.continuousQuotientHom_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T00:10:39.987018+00:00
-- url     : https://prove2.me/theorems/c40e94c9-d4ba-4099-942a-3540cb9eb1ba
-- title:
--   The actual norm quotient Kummer group homomorphism into continuous H1 is injective
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, and phi a finite internal group endomorphism with surjective K-point map. The original continuous norm quotient Kummer group homomorphism $$P(\mathbb Q)/\varphi(P(\mathbb Q))\longrightarrow H^1_{\mathrm{cont}}(\operatorname{Aut}_{\mathbb Q}(K),\ker(\varphi)(K))$$ is injective. Under the forgetful map it recovers the original algebraic quotient Kummer homomorphism. This is used for the concrete actual norm maps and subsequent local Selmer bounds; no algebraic-closure assumption is added.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousKummerInjection.continuousQuotientHom_injective, full original statement and proof body retained, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual rational norm quotients inject by group
homomorphisms into continuous H1 of the actual geometric norm kernels.
The checked forgetful maps recover the prior algebraic Kummer maps.
Named downstream consumer: the local Selmer conditions and rank-zero bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousKummerGenericGroupHomData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormKummerGroupHom_quotientHom_injective
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
local instance publicContinuousNormQuotientInjectiveStatementProvider920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicContinuousNormQuotientInjectiveStatementProvider1020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicContinuousNormQuotientInjectiveStatementProvider1120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicContinuousNormQuotientInjectiveStatementProvider1220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicContinuousNormQuotientInjectiveStatementProvider1320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicContinuousNormQuotientInjectiveStatementProvider1420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicContinuousNormQuotientInjectiveStatementProvider1520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicContinuousNormQuotientInjectiveStatementProvider1620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection
open MazurTransfer.Order13ActualPicardNormContinuousCohomology
open MazurTransfer.Order13ActualPicardNormContinuousKummerInjection

theorem MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.continuousQuotientHom_injective (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    (hsurj : Function.Surjective (normHom K φ)) : Function.Injective (continuousQuotientHom K φ hsurj) := by sorry
