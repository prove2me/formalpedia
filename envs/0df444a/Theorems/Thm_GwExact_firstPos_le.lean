-- Prove2me | Theorems.Thm_GwExact_firstPos_le
-- name    : GwExact.firstPos_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:20:56.814594+00:00
-- url     : https://prove2.me/theorems/06e8faf2-68d5-4063-8538-c42940a8eb5e
-- title:
--   Gw Exact: first Pos le
-- statement:
--   The Gw Exact construction uses the first Pos le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L40-L41
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L40-L41

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
set_option autoImplicit true
@[expose] public section
public section
open GwExact
variable {α : Type*} [DecidableEq α] (f : ℕ → α)

theorem GwExact.firstPos_le (i : ℕ) : firstPos f i ≤ i := by sorry
