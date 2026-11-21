-- Prove2me | Theorems.Thm_GwExact_shiftRight_one
-- name    : GwExact.shiftRight_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:18:45.24363+00:00
-- url     : https://prove2.me/theorems/6fa91d9b-856d-4f71-9c8e-88b0181e2665
-- title:
--   Gw Exact: shift Right one
-- statement:
--   The Gw Exact construction uses the shift Right one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L127-L129
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L127-L129

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.shiftRight_one (k : Nat) : Nat.shiftRight k 1 = k / 2 := by sorry
