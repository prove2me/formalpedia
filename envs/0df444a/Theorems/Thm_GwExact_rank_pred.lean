-- Prove2me | Theorems.Thm_GwExact_rank_pred
-- name    : GwExact.rank_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:06.253534+00:00
-- url     : https://prove2.me/theorems/b1833bdf-7729-41e1-a9bb-95f98483beef
-- title:
--   Gw Exact: rank pred
-- statement:
--   A rank `k ≥ 1` at position `i` occurs as rank `k - 1` at an earlier position.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L122-L124
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L122-L124

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

theorem GwExact.rank_pred {i : ℕ} (h : 1 ≤ rank f i) : ∃ j < i, rank f j + 1 = rank f i := by sorry
