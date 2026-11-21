-- Prove2me | Theorems.Thm_GwExact_testBit_lor
-- name    : GwExact.testBit_lor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:19:32.274073+00:00
-- url     : https://prove2.me/theorems/c5ba51ec-1dfc-4ee6-b4f0-8f3582faf1fa
-- title:
--   Gw Exact: test Bit lor
-- statement:
--   The Gw Exact construction uses the test Bit lor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L241-L242
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L241-L242

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.testBit_lor (a b v : Nat) : (Nat.lor a b).testBit v = (a.testBit v || b.testBit v) := by sorry
