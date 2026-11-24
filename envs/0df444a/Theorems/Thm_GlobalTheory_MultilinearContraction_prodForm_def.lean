-- Prove2me | Theorems.Thm_GlobalTheory_MultilinearContraction_prodForm_def
-- name    : GlobalTheory.MultilinearContraction.prodForm_def
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:23.097794+00:00
-- url     : https://prove2.me/theorems/82450b85-8c7e-4f17-b0f6-e9818d4dd5d6
-- title:
--   Multilinear Contraction: prod Form def
-- statement:
--   The Multilinear Contraction construction uses the prod Form def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean#L82-L83

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
variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

theorem GlobalTheory.MultilinearContraction.prodForm_def (φ : ∀ i, X i →ₗ[R] R) :
    prodForm φ = PiTensorProduct.lift (prodMultilinear φ) := by sorry
