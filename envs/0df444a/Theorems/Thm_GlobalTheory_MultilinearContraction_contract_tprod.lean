-- Prove2me | Theorems.Thm_GlobalTheory_MultilinearContraction_contract_tprod
-- name    : GlobalTheory.MultilinearContraction.contract_tprod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:02.108956+00:00
-- url     : https://prove2.me/theorems/9b66e6a7-7b53-4994-95a9-ea58182f1193
-- title:
--   Multilinear Contraction: contract tprod
-- statement:
--   The Multilinear Contraction construction uses the contract tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean#L62-L64

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

theorem GlobalTheory.MultilinearContraction.contract_tprod (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contract φ j (⨂ₜ[R] i, x i) = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := by sorry
