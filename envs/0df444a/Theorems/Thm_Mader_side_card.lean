-- Prove2me | Theorems.Thm_Mader_side_card
-- name    : Mader.side_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:52:03.757612+00:00
-- url     : https://prove2.me/theorems/bb4434ca-e505-4b33-bb00-95b7241c3d19
-- title:
--   Mader: side card
-- statement:
--   The Mader construction uses the side card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderSteps.lean#L32-L43
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderSteps.lean#L32-L43

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Definitions.Def_MaderLib_MaderSteps
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*} (G : SimpleGraph V)

theorem Mader.side_card [DecidableEq V] {S U X : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n) {x : V} (hxS : x ∈ S)
    (hnb : ∀ w ∈ S, G.Adj x w → w ∈ U ∪ X) : 2 * k < (U ∪ X).card := by sorry
