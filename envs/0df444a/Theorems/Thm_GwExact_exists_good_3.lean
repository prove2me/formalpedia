-- Prove2me | Theorems.Thm_GwExact_exists_good_3
-- name    : GwExact.exists_good_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:24:30.116955+00:00
-- url     : https://prove2.me/theorems/5e852abb-e773-4c49-b67b-22bf91d0a6a8
-- title:
--   Gw Exact: exists good 3
-- statement:
--   The Gw Exact construction uses the exists good 3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/Solution.lean#L25-L25
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/Solution.lean#L25-L25

module
public import Definitions.Def_GwExact
public import Definitions.Def_GwExactSolution
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.exists_good_3 : ∃ c : ℕ → Fin 3, IsGoodExactColouring 3 4 52 c := by sorry
