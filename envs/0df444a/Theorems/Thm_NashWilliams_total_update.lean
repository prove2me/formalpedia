-- Prove2me | Theorems.Thm_NashWilliams_total_update
-- name    : NashWilliams.total_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:41:20.650562+00:00
-- url     : https://prove2.me/theorems/8058edc4-d303-4172-a204-fdef385078d5
-- title:
--   Nash Williams: total update
-- statement:
--   The Nash Williams construction uses the total update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L190-L198
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L190-L198

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable (G : SimpleGraph V) {k : ℕ}
variable {G}

theorem NashWilliams.total_update (F : Fin k → SimpleGraph V) (i : Fin k) (X : SimpleGraph V) :
    total (update F i X) + (F i).edgeSet.ncard = total F + X.edgeSet.ncard := by sorry
