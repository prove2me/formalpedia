-- Prove2me | Theorems.Thm_GwExact_testBit_bit
-- name    : GwExact.testBit_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:20:20.48725+00:00
-- url     : https://prove2.me/theorems/43d8a19d-5569-49c1-b6fe-97dbea849690
-- title:
--   Gw Exact: test Bit bit
-- statement:
--   The Gw Exact construction uses the test Bit bit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L108-L110
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L108-L110

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.testBit_bit (v u : Nat) : (bit v).testBit u = decide (v = u) := by sorry
