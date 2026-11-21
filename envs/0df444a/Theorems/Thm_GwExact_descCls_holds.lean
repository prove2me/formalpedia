-- Prove2me | Theorems.Thm_GwExact_descCls_holds
-- name    : GwExact.descCls_holds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:21:15.784041+00:00
-- url     : https://prove2.me/theorems/1a1d7411-c02c-4a68-aab8-220777581ca4
-- title:
--   Gw Exact: desc Cls holds
-- statement:
--   Every clause computed from a descriptor is true for the assignment of a colouring with the
--   properties `GoodPos`.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L158-L260
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L158-L260

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.descCls_holds {n R l : Nat} {col : Nat → Nat} (hcol : GoodPos n R l col) (code : Nat)
    {cl : Cls} (h : descCls n R l code = some cl) : cl.Holds (asg R col) := by sorry
