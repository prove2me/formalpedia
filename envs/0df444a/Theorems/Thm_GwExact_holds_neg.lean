-- Prove2me | Theorems.Thm_GwExact_holds_neg
-- name    : GwExact.holds_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:20:44.551522+00:00
-- url     : https://prove2.me/theorems/12bd7986-01f9-410b-b055-20312443132a
-- title:
--   Gw Exact: holds neg
-- statement:
--   A negative literal "position `i` does not have colour `c`" that is true makes the clause true.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L141-L143
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L141-L143

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.holds_neg {R : Nat} {col : Nat → Nat} {cl : Cls} {i c : Nat} (hc : c < R)
    (hbit : cl.n.testBit (i * R + c) = true) (hne : col i ≠ c) : cl.Holds (asg R col) := by sorry
