-- Prove2me | Theorems.Thm_GwExact_notMem_firstPos
-- name    : GwExact.notMem_firstPos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:51.791906+00:00
-- url     : https://prove2.me/theorems/ab887a72-126e-4185-8c58-bfdbe07c1eaa
-- title:
--   Gw Exact: not Mem first Pos
-- statement:
--   The Gw Exact construction uses the not Mem first Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L66-L69
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L66-L69

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

theorem GwExact.notMem_firstPos (i : ℕ) : f (firstPos f i) ∉ (Finset.range (firstPos f i)).image f := by sorry
