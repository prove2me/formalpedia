-- Prove2me | Theorems.Thm_Mader_ndeg_le_card
-- name    : Mader.ndeg_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:30.559112+00:00
-- url     : https://prove2.me/theorems/ec6df8c5-f308-467d-846d-f248ba2884b6
-- title:
--   Mader: ndeg le card
-- statement:
--   The Mader construction uses the ndeg le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L54-L61
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L54-L61

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)

theorem Mader.ndeg_le_card {S T : Finset V} {v : V} (h : ∀ w ∈ S, G.Adj v w → w ∈ T) :
    ndeg G S v ≤ T.card := by sorry
