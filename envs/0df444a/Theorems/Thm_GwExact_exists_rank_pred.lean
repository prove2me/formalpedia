-- Prove2me | Theorems.Thm_GwExact_exists_rank_pred
-- name    : GwExact.exists_rank_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:08.49316+00:00
-- url     : https://prove2.me/theorems/24476fd8-ed5b-4316-9087-928678006142
-- title:
--   Gw Exact: exists rank pred
-- statement:
--   The Gw Exact construction uses the exists rank pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L100-L119
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L100-L119

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

theorem GwExact.exists_rank_pred : ∀ m, 1 ≤ numCols f m → ∃ j < m, rank f j + 1 = numCols f m := by sorry
