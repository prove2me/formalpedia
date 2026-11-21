-- Prove2me | Theorems.Thm_GwExact_rank_lt_card
-- name    : GwExact.rank_lt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:11.643012+00:00
-- url     : https://prove2.me/theorems/829fd85e-7dd9-4ee7-9c73-8c30a5fd82ef
-- title:
--   Gw Exact: rank lt card
-- statement:
--   With `r` colours, every rank is below `r`.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L129-L138
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L129-L138

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

theorem GwExact.rank_lt_card {r : ℕ} (f : ℕ → Fin r) (i : ℕ) : rank f i < r := by sorry
