-- Prove2me | Theorems.Thm_GwExact_holds_pos
-- name    : GwExact.holds_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:20:47.498916+00:00
-- url     : https://prove2.me/theorems/a56d8bae-c669-4053-b338-c000ac3995ce
-- title:
--   Gw Exact: holds pos
-- statement:
--   A positive literal "position `i` has colour `c`" that is true makes the clause true.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L146-L148
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L146-L148

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.holds_pos {R : Nat} {col : Nat → Nat} {cl : Cls} {i c : Nat} (hc : c < R)
    (hbit : cl.p.testBit (i * R + c) = true) (heq : col i = c) : cl.Holds (asg R col) := by sorry
