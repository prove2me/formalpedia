-- Prove2me | Theorems.Thm_GlobalTheory_tensor_pairing_separating
-- name    : GlobalTheory.tensor_pairing_separating
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:49.537144+00:00
-- url     : https://prove2.me/theorems/1f1adb37-f617-4684-8cf7-f887e45fc8cf
-- title:
--   Global Theory: tensor pairing separating
-- statement:
--   The Global Theory construction uses the tensor pairing separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorProductNondegeneratePairing.lean#L21-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorProductNondegeneratePairing.lean#L21-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorProductNondegeneratePairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module

theorem GlobalTheory.tensor_pairing_separating : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)]
    [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ),
    (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) →
    ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)),
      (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧
      ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by sorry
