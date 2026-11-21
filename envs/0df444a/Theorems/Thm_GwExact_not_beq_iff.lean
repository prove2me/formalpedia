-- Prove2me | Theorems.Thm_GwExact_not_beq_iff
-- name    : GwExact.not_beq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:09.501179+00:00
-- url     : https://prove2.me/theorems/1ef255cd-1633-4183-bf7c-cc18780c5e18
-- title:
--   Gw Exact: not beq iff
-- statement:
--   The Gw Exact construction uses the not beq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L150-L154
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L150-L154

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.not_beq_iff (a b : Nat) : (!Nat.beq a b) = true ↔ a ≠ b := by sorry
