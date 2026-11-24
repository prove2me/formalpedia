-- Prove2me | Theorems.Thm_GlobalTheory_perm_invariant_of_cons_swap
-- name    : GlobalTheory.perm_invariant_of_cons_swap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:56.350823+00:00
-- url     : https://prove2.me/theorems/8dec2139-9f80-4c83-aae5-775493e095a7
-- title:
--   Global Theory: perm invariant of cons swap
-- statement:
--   The Global Theory construction uses the perm invariant of cons swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PermInvariantOfConsSwapAndTail.lean#L5-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PermInvariantOfConsSwapAndTail.lean#L5-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermInvariantOfConsSwapAndTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Equiv

theorem GlobalTheory.perm_invariant_of_cons_swap :
  ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by sorry
