-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_eigenSub_baseChangeAction
-- name    : GlobalTheory.EigenSplit.eigenSub_baseChangeAction
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:23.669363+00:00
-- url     : https://prove2.me/theorems/a0f099eb-f42b-4a51-860b-f4a36f3724f3
-- title:
--   Eigen Split: eigen Sub base Change Action
-- statement:
--   The Eigen Split construction uses the eigen Sub base Change Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L473-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L473-L483

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

theorem GlobalTheory.EigenSplit.eigenSub_baseChangeAction [Finite ι] (h : IsSplitting σ) (i : ι) :
    eigenSub (baseChangeAction R' ρ) ((algebraMap R R').comp (σ i))
      = (eigenSub ρ (σ i)).baseChange R' := by sorry
