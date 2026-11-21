-- Prove2me | Theorems.Thm_GwExact_testBit_rem
-- name    : GwExact.testBit_rem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:19:06.225656+00:00
-- url     : https://prove2.me/theorems/b600f9cd-f2f6-4327-b57a-3608c4f0db69
-- title:
--   Gw Exact: test Bit rem
-- statement:
--   The Gw Exact construction uses the test Bit rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L235-L239
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L235-L239

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.testBit_rem (a b v : Nat) :
    (Nat.xor a (Nat.land a b)).testBit v = (a.testBit v && !b.testBit v) := by sorry
