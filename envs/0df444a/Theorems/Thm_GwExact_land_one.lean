-- Prove2me | Theorems.Thm_GwExact_land_one
-- name    : GwExact.land_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:18:43.818902+00:00
-- url     : https://prove2.me/theorems/02747f08-b65b-4902-99f5-abaf085a92e6
-- title:
--   Gw Exact: land one
-- statement:
--   The Gw Exact construction uses the land one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L125-L125
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L125-L125

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.land_one (k : Nat) : Nat.land k 1 = k % 2 := by sorry
