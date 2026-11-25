-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_exists_clear_col
-- name    : GlobalTheory.UnipotentInvariant.exists_clear_col
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:35.542776+00:00
-- url     : https://prove2.me/theorems/3c341092-0e3d-4c9f-aa2f-f0b075cd2791
-- title:
--   Unipotent Invariant: exists clear col
-- statement:
--   The Unipotent Invariant construction uses the exists clear col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L86-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L86-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}

theorem GlobalTheory.UnipotentInvariant.exists_clear_col (n : Fin p) (M : Matrix (Fin p) (Fin p) K) (hn : M n n ≠ 0) :
    ∃ M' : Matrix (Fin p) (Fin p) K, (∀ f, BiInvariant f → f M' = f M) ∧
      (∀ b, n < b → M' b n = 0) ∧ (∀ b k, b ≤ n → M' b k = M b k) ∧
      (∀ b k, M n k = 0 → M' b k = M b k) := by sorry
