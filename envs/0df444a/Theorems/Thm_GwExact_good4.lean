-- Prove2me | Theorems.Thm_GwExact_good4
-- name    : GwExact.good4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:18:20.717177+00:00
-- url     : https://prove2.me/theorems/4d6c4cbb-ec80-4805-84c5-ce20ea5477c0
-- title:
--   Gw Exact: good4
-- statement:
--   The Gw Exact construction uses the good4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Lower.lean#L79-L79
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Lower.lean#L79-L79

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Lower
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.good4 : IsGoodExactColouring 4 4 52 col4 := by sorry
