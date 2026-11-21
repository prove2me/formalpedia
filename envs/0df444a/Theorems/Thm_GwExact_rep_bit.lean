-- Prove2me | Theorems.Thm_GwExact_rep_bit
-- name    : GwExact.rep_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:20:33.173245+00:00
-- url     : https://prove2.me/theorems/b37bc126-945e-4467-a75b-bbc116a92f66
-- title:
--   Gw Exact: rep bit
-- statement:
--   The Gw Exact construction uses the rep bit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L128-L138
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L128-L138

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.rep_bit (R : Nat) : ∀ i j, j < i → (rep R i).testBit (j * R) = true := by sorry
