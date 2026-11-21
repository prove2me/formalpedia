-- Prove2me | Theorems.Thm_GwExact_gwProperty_53_of_le
-- name    : GwExact.gwProperty_53_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:36.277759+00:00
-- url     : https://prove2.me/theorems/d55f6e47-59c1-4101-8076-857641dc3b0f
-- title:
--   Gw Exact: gw Property 53 of le
-- statement:
--   For `r ≤ 5` colours: every colouring of `[1, n]`, `n ≥ 53`, has a rainbow 3-term AP or a
--   monochromatic 4-term AP.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Upper.lean#L23-L23
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Upper.lean#L23-L23

module
public import Definitions.Def_GwExact_Rank
public import Definitions.Def_GwExact_Cert
public import Definitions.Def_GwExact_Upper
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.gwProperty_53_of_le {r : ℕ} (hr : r ≤ 5) : GWProperty r 4 53 := by sorry
