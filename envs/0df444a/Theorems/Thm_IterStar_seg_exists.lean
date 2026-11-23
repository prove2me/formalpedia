-- Prove2me | Theorems.Thm_IterStar_seg_exists
-- name    : IterStar_seg_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:24:52.475005+00:00
-- url     : https://prove2.me/theorems/093dab0a-83a9-4665-bb29-d76a90eeaff6
-- title:
--   Iter Star seg exists: Iter Star seg exists
-- statement:
--   The Iter Star seg exists construction uses the Iter Star seg exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L202-L211
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L202-L211

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem IterStar_seg_exists {L : Set (List A)} {al : List A} (h : al ∈ L∗) :
    ∃ n, ∃ φ : Stream' ℕ, StrictMonoOn φ {k | k < n + 1} ∧ φ 0 = 0 ∧ φ n = al.length ∧
      ∀ k < n, al.extract (φ k) (φ (k + 1)) ∈ L := by sorry
