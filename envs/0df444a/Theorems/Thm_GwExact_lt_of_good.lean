-- Prove2me | Theorems.Thm_GwExact_lt_of_good
-- name    : GwExact.lt_of_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:21.605603+00:00
-- url     : https://prove2.me/theorems/f61e035c-ba13-472e-9438-816090d26c1e
-- title:
--   Gw Exact: lt of good
-- statement:
--   A good exact colouring of `[1, n]` puts every GW threshold above `n`.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L179-L182
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L179-L182

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

theorem GwExact.lt_of_good {r l n : ℕ} {c : ℕ → Fin r} (hc : IsGoodExactColouring r l n c) {m : ℕ}
    (hm : GWProperty r l m) : n < m := by sorry
