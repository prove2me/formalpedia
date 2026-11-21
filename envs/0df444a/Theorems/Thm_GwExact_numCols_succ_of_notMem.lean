-- Prove2me | Theorems.Thm_GwExact_numCols_succ_of_notMem
-- name    : GwExact.numCols_succ_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:08.293973+00:00
-- url     : https://prove2.me/theorems/77f13257-239a-4e3b-ab12-f673e1abf719
-- title:
--   Gw Exact: num Cols succ of not Mem
-- statement:
--   The Gw Exact construction uses the num Cols succ of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L62-L64
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L62-L64

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

theorem GwExact.numCols_succ_of_notMem {m : ℕ} (h : f m ∉ (Finset.range m).image f) :
    numCols f (m + 1) = numCols f m + 1 := by sorry
