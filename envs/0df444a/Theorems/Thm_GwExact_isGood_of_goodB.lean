-- Prove2me | Theorems.Thm_GwExact_isGood_of_goodB
-- name    : GwExact.isGood_of_goodB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:18:17.135188+00:00
-- url     : https://prove2.me/theorems/e0aca139-5135-41cc-a447-b7c53a28b53e
-- title:
--   Gw Exact: is Good of good B
-- statement:
--   The Gw Exact construction uses the is Good of good B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Lower.lean#L38-L62
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Lower.lean#L38-L62

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Lower
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.isGood_of_goodB {r l n : ℕ} {c : ℕ → Fin r} (hl : 2 ≤ l) (h : goodB r l n c = true) :
    IsGoodExactColouring r l n c := by sorry
