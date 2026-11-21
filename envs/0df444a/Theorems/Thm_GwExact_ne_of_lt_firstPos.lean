-- Prove2me | Theorems.Thm_GwExact_ne_of_lt_firstPos
-- name    : GwExact.ne_of_lt_firstPos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:04.158541+00:00
-- url     : https://prove2.me/theorems/db924511-9a41-4831-8911-6a4e08ab5906
-- title:
--   Gw Exact: ne of lt first Pos
-- statement:
--   The Gw Exact construction uses the ne of lt first Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L43-L44
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L43-L44

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

theorem GwExact.ne_of_lt_firstPos {i j : ℕ} (h : j < firstPos f i) : f j ≠ f i := by sorry
