-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- name    : GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:35.399592+00:00
-- url     : https://prove2.me/theorems/ed9a28e5-3000-4834-ab34-a9c0880dda5f
-- title:
--   Eigen Split: coe eigen Base Change Equiv tmul
-- statement:
--   The Eigen Split construction uses the coe eigen Base Change Equiv tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L459-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L459-L462

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {R' : Type*} [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
  {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R' M} {f : N →ₗ[R] M}
variable {σ : ι → O →+* R}
variable (R') (ρ)

theorem GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul [Finite ι] (h : IsSplitting σ) (i : ι) (r : R')
    (x : eigenSub ρ (σ i)) :
    (eigenBaseChangeEquiv R' ρ h i (r ⊗ₜ x) : R' ⊗[R] N) = r ⊗ₜ (x : N) := by sorry
