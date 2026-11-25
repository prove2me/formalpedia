-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_linearIndependent_products_function_field
-- name    : GlobalTheory.T.exists_linearIndependent_products_function_field
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:31:09.013549+00:00
-- url     : https://prove2.me/theorems/5d3574ff-9006-581b-9205-e7d3dab2c00f
-- title:
--   T: exists linear Independent products function field
-- statement:
--   The T construction uses the exists linear Independent products function field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ManyIndependentProductsInFunctionFieldStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ManyIndependentProductsInFunctionFieldStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ManyIndependentProductsInFunctionField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ManyIndependentProductsInFunctionFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_linearIndependent_products_function_field : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K), LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K, LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧ v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by sorry
