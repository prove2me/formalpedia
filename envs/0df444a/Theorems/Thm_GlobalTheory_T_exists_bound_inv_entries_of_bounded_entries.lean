-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_bound_inv_entries_of_bounded_entries
-- name    : GlobalTheory.T.exists_bound_inv_entries_of_bounded_entries
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:44.49119+00:00
-- url     : https://prove2.me/theorems/cc16fe4f-3ae7-4ede-875d-7669fadd48b0
-- title:
--   T: exists bound inv entries of bounded entries
-- statement:
--   The T construction uses the exists bound inv entries of bounded entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MatrixInvEntriesBoundedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MatrixInvEntriesBoundedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MatrixInvEntriesBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MatrixInvEntriesBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_bound_inv_entries_of_bounded_entries : ∀ (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ), Continuous G → (∀ c, G c ≠ 0 → IsUnit c) → ∀ B ε : ℝ, 0 < ε → ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by sorry
