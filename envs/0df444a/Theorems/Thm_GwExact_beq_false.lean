-- Prove2me | Theorems.Thm_GwExact_beq_false
-- name    : GwExact.beq_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:19:15.934451+00:00
-- url     : https://prove2.me/theorems/48ab2b75-a025-429e-ad7a-9642da48d6d9
-- title:
--   Gw Exact: beq false
-- statement:
--   The Gw Exact construction uses the beq false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L244-L247
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L244-L247

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.beq_false {a b : Nat} (h : ¬ a = b) : Nat.beq a b = false := by sorry
