-- Prove2me | Theorems.Thm_GwExact_numCols_mono
-- name    : GwExact.numCols_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:36.646443+00:00
-- url     : https://prove2.me/theorems/9ea79306-94af-4eef-8a9c-9971a5e78e10
-- title:
--   Gw Exact: num Cols mono
-- statement:
--   The Gw Exact construction uses the num Cols mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L55-L56
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L55-L56

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

theorem GwExact.numCols_mono {m m' : ℕ} (h : m ≤ m') : numCols f m ≤ numCols f m' := by sorry
