-- Prove2me | Theorems.Thm_GwExact_rank_eq_iff
-- name    : GwExact.rank_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:59.331494+00:00
-- url     : https://prove2.me/theorems/0a3b78c0-ea3f-45dc-898a-8f5896b1ba29
-- title:
--   Gw Exact: rank eq iff
-- statement:
--   The renaming keeps the equal/unequal pattern of the colouring.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L81-L94
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L81-L94

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

theorem GwExact.rank_eq_iff {i i' : ℕ} : rank f i = rank f i' ↔ f i = f i' := by sorry
