-- Prove2me | Theorems.Thm_GwExact_firstPos_congr
-- name    : GwExact.firstPos_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:30.803202+00:00
-- url     : https://prove2.me/theorems/3637d114-9562-448d-a716-c1ffc6b8782a
-- title:
--   Gw Exact: first Pos congr
-- statement:
--   The Gw Exact construction uses the first Pos congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L46-L48
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L46-L48

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

theorem GwExact.firstPos_congr {i i' : ℕ} (h : f i = f i') : firstPos f i = firstPos f i' := by sorry
