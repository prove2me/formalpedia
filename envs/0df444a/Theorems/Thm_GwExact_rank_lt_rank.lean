-- Prove2me | Theorems.Thm_GwExact_rank_lt_rank
-- name    : GwExact.rank_lt_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:59.18662+00:00
-- url     : https://prove2.me/theorems/303f5afe-65a3-4744-a9f5-28473edd153b
-- title:
--   Gw Exact: rank lt rank
-- statement:
--   The Gw Exact construction uses the rank lt rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L74-L78
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L74-L78

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

theorem GwExact.rank_lt_rank {i i' : ℕ} (h : firstPos f i < firstPos f i') : rank f i < rank f i' := by sorry
