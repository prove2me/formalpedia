-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormSubgroupRestriction_restrictedClass_zero_iff_subgroup_invariant_preimage
-- name    : MazurTransfer.Order13ActualPicardNormSubgroupRestriction.restrictedClass_zero_iff_subgroup_invariant_preimage
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T00:38:09.26596+00:00
-- url     : https://prove2.me/theorems/75593220-2d15-4fea-bf42-5cd35e050d27
-- title:
--   An actual norm class restricts to zero exactly for subgroup-invariant norm preimages
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, phi a finite internal group endomorphism, and S any subgroup of Aut_Q(K) with its induced topology. If b is a K-valued preimage of a rational point a, then $$\operatorname{res}_S[b]_{\mathrm{cont}}=0\quad\Longleftrightarrow\quad\exists c\in P(K),\ \varphi(c)=a\ \text{and}\ \forall\sigma\in S,\ \sigma(c)=c.$$ This is the original subgroup norm-class zero criterion for decomposition-group local conditions. No arithmetic identification of S is assumed or concluded.
-- source:
--   Original MazurTheorem Order13ActualPicardNormSubgroupRestriction.restrictedClass_zero_iff_subgroup_invariant_preimage, with original main proof and the original generic NormCocycleInvariantPreimageCriterion helper in a distinct namespace, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restriction of actual continuous norm classes to Galois
subgroups has zero class exactly when there is a subgroup-invariant norm
preimage. Named downstream consumer: decomposition-group local conditions.
No arithmetic identification of decomposition groups is asserted here.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: triviality of a kernel-valued preimage cocycle is
equivalent to the existence of an invariant preimage.
Named downstream consumer: the zero criterion for actual Picard norm
classes in Mathlib algebraic group cohomology.
-/


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
local instance publicNormSubgroupInvariantStatementProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicNormSubgroupInvariantStatementProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicNormSubgroupInvariantStatementProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicNormSubgroupInvariantStatementProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance publicNormSubgroupInvariantStatementProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance publicNormSubgroupInvariantStatementProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicNormSubgroupInvariantStatementProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicNormSubgroupInvariantStatementProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormContinuousCohomology

open MazurTransfer.Order13ActualPicardNormSubgroupRestriction

theorem MazurTransfer.Order13ActualPicardNormSubgroupRestriction.restrictedClass_zero_iff_subgroup_invariant_preimage (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    (S : Subgroup (K ≃ₐ[ℚ] K))
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    restrictNormClass K φ S (continuousClassOfLift K φ a b hb) = 0 ↔
      ∃ c : Points K, c ≫ φ = rationalPoint K a ∧ ∀ σ : S, actionHom K σ.val c = c := by sorry
