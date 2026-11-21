-- Prove2me | Theorems.Thm_GwExact_firstPos_spec
-- name    : GwExact.firstPos_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:20:53.559568+00:00
-- url     : https://prove2.me/theorems/a777e7f9-40bd-48f7-9566-4d0d8b28d5b2
-- title:
--   Gw Exact: first Pos spec
-- statement:
--   The Gw Exact construction uses the first Pos spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L37-L38
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L37-L38

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

theorem GwExact.firstPos_spec (i : ℕ) : f (firstPos f i) = f i := by sorry
