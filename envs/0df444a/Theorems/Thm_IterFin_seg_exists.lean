-- Prove2me | Theorems.Thm_IterFin_seg_exists
-- name    : IterFin_seg_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:24:51.133818+00:00
-- url     : https://prove2.me/theorems/7f4667e2-efb3-45cf-acc4-86d462331f77
-- title:
--   Iter Fin seg exists: Iter Fin seg exists
-- statement:
--   The Iter Fin seg exists construction uses the Iter Fin seg exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L167-L200
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L167-L200

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem IterFin_seg_exists {L : Set (List A)} {m : ℕ} {al : List A} (h : al ∈ L ^ m) :
    ∃ n ≤ m, ∃ φ : Stream' ℕ, StrictMonoOn φ {k | k < n + 1} ∧ φ 0 = 0 ∧ φ n = al.length ∧
      ∀ k < n, al.extract (φ k) (φ (k + 1)) ∈ L := by sorry
