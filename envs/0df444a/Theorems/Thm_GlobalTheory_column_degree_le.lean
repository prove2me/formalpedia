-- Prove2me | Theorems.Thm_GlobalTheory_column_degree_le
-- name    : GlobalTheory.column_degree_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:16.043936+00:00
-- url     : https://prove2.me/theorems/c17de67a-0db9-45c6-84ff-34b61441c945
-- title:
--   Global Theory: column degree le
-- statement:
--   The Global Theory construction uses the column degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ColumnDegreeLe.lean#L66-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ColumnDegreeLe.lean#L66-L266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ColumnDegreeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem GlobalTheory.column_degree_le {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) (lam : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = lam a)
    (hinv : ∀ a b : Fin p, a < b → ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (S : Finset (Fin n)) : ∀ m ∈ P.support,
      ∑ a, ∑ k ∈ S, m (z (a, k)) ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card), lam a := by sorry
