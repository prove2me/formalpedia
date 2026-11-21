-- Prove2me | Theorems.Thm_GwExact_gwProperty_of_check
-- name    : GwExact.gwProperty_of_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:17.760699+00:00
-- url     : https://prove2.me/theorems/5decdaa8-0745-48cd-b3eb-6026b872afdf
-- title:
--   Gw Exact: gw Property of check
-- statement:
--   A certificate accepted by the checker for `(n, R, l)` gives the GW property at `n` for every
--   number `r ≤ R` of colours.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L171-L176
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L171-L176

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

theorem GwExact.gwProperty_of_check {r R l n : ℕ} (hrR : r ≤ R) {steps : List Nat}
    (h : checkGw n R l steps = true) : GWProperty r l n := by sorry
