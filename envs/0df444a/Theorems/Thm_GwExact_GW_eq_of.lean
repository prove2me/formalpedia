-- Prove2me | Theorems.Thm_GwExact_GW_eq_of
-- name    : GwExact.GW_eq_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:24.091122+00:00
-- url     : https://prove2.me/theorems/c94d815b-7b87-40e5-90a2-a7a6aa62c9bf
-- title:
--   Gw Exact: GW eq of
-- statement:
--   A good exact `r`-colouring of `[1, n]` and the GW property at `n + 1` pin down `GW r l = n + 1`.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L185-L187
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L185-L187

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.GW_eq_of {r l n : ℕ} {c : ℕ → Fin r} (hgood : IsGoodExactColouring r l n c)
    (hup : GWProperty r l (n + 1)) : GW r l = n + 1 := by sorry
