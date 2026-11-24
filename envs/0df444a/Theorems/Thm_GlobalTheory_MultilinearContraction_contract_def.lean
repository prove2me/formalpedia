-- Prove2me | Theorems.Thm_GlobalTheory_MultilinearContraction_contract_def
-- name    : GlobalTheory.MultilinearContraction.contract_def
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:33.777265+00:00
-- url     : https://prove2.me/theorems/c7c3603d-54f0-4b4c-88a3-b26f04849a09
-- title:
--   Multilinear Contraction: contract def
-- statement:
--   The Multilinear Contraction construction uses the contract def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean#L59-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ContractMultilinearApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct BigOperators
open GlobalTheory GlobalTheory.MultilinearContraction
variable {ι : Type*} [Fintype ι] [dι : DecidableEq ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

theorem GlobalTheory.MultilinearContraction.contract_def (φ : ∀ i, X i →ₗ[R] R) (j : ι) :
    contract φ j = PiTensorProduct.lift (contractMultilinear φ j) := by sorry
