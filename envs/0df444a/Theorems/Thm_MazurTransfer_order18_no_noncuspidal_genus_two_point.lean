-- Prove2me | Theorems.Thm_MazurTransfer_order18_no_noncuspidal_genus_two_point
-- name    : MazurTransfer.order18_no_noncuspidal_genus_two_point
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T13:39:49.465219+00:00
-- url     : https://prove2.me/theorems/2f9a6f2a-8be6-4621-b336-3a39746e78d0
-- title:
--   Order18: unconditional rational noncuspidal exclusion on the exact genus-two sextic
-- statement:
--   There are no rational x,y satisfying y²=x⁶−4x⁵+10x⁴−10x³+5x²−2x+1 with x≠0 and x≠1. This is unconditional. The exact sextic and both cusp exclusions are preserved.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, original Apache-2.0 headers and attribution retained. Closure of the exact original no_noncuspidal_point is selected from kernel dependency facts and complete original Lean AST declaration ranges. It has 2208 reachable declarations in 20627 lines. The new interface expands the original hyperelliptic polynomial definition and preserves every hypothesis. Named downstream consumers: MazurTransfer.order18_from_genus_two_exclusion and MazurCampaign.no_order_eighteen. This splits the retained 21755-line full proof whose server submission timed out after300s; the unchanged campaign statement remains unconditional. Official Anthropic FLT division-polynomial lemma is reused at the same exact Mathlib pin.

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
open scoped WeierstrassCurve.Affine

theorem MazurTransfer.order18_no_noncuspidal_genus_two_point (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve : y ^ 2 = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1) : False := by sorry
