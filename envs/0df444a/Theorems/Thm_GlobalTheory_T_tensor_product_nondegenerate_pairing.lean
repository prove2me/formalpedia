-- Prove2me | Theorems.Thm_GlobalTheory_T_tensor_product_nondegenerate_pairing
-- name    : GlobalTheory.T.tensor_product_nondegenerate_pairing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:54.937795+00:00
-- url     : https://prove2.me/theorems/a259d81a-d9d3-4909-8589-034f4a4a6354
-- title:
--   T: tensor product nondegenerate pairing
-- statement:
--   The T construction uses the tensor product nondegenerate pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorProductNondegeneratePairingStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorProductNondegeneratePairingStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorProductNondegeneratePairing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorProductNondegeneratePairingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tensor_product_nondegenerate_pairing : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type) [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)] [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ), (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) → ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)), (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧ ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by sorry
