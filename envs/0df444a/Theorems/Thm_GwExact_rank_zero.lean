-- Prove2me | Theorems.Thm_GwExact_rank_zero
-- name    : GwExact.rank_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:02.28634+00:00
-- url     : https://prove2.me/theorems/dce37d92-d735-41f9-9e3e-071b80f7ada9
-- title:
--   Gw Exact: rank zero
-- statement:
--   The Gw Exact construction uses the rank zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L96-L98
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L96-L98

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

theorem GwExact.rank_zero : rank f 0 = 0 := by sorry
