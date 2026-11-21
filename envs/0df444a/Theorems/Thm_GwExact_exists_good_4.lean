-- Prove2me | Theorems.Thm_GwExact_exists_good_4
-- name    : GwExact.exists_good_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:24:38.505513+00:00
-- url     : https://prove2.me/theorems/3ef971e6-1710-4d53-8200-dff9f6b9e895
-- title:
--   Gw Exact: exists good 4
-- statement:
--   The Gw Exact construction uses the exists good 4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/Solution.lean#L27-L27
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/Solution.lean#L27-L27

module
public import Definitions.Def_GwExact
public import Definitions.Def_GwExactSolution
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.exists_good_4 : ∃ c : ℕ → Fin 4, IsGoodExactColouring 4 4 52 c := by sorry
