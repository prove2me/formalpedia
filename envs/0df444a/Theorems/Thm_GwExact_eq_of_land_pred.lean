-- Prove2me | Theorems.Thm_GwExact_eq_of_land_pred
-- name    : GwExact.eq_of_land_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:19:05.285015+00:00
-- url     : https://prove2.me/theorems/c94acc38-4cb6-4e35-8aa8-bbb88e2aa328
-- title:
--   Gw Exact: eq of land pred
-- statement:
--   `x &&& (x - 1) = 0` leaves at most one bit of `x` set.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L191-L233
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L191-L233

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.eq_of_land_pred (x : Nat) : Nat.land x (x - 1) = 0 →
    ∀ u v, x.testBit u = true → x.testBit v = true → u = v := by sorry
