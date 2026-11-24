-- Prove2me | Theorems.Thm_GlobalTheory_matrix_inv_entries_bounded
-- name    : GlobalTheory.matrix_inv_entries_bounded
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:09:33.255345+00:00
-- url     : https://prove2.me/theorems/2d2a34bd-ce69-4210-b3fe-79964030be5b
-- title:
--   Global Theory: matrix inv entries bounded
-- statement:
--   The Global Theory construction uses the matrix inv entries bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MatrixInvEntriesBounded.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MatrixInvEntriesBounded.lean#L7-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MatrixInvEntriesBounded
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
open GlobalTheory

theorem GlobalTheory.matrix_inv_entries_bounded (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ) (hG : Continuous G) (hU : ∀ c, G c ≠ 0 → IsUnit c) (B ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by sorry
