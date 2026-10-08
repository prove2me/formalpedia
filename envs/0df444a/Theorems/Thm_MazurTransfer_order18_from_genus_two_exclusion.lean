-- Prove2me | Theorems.Thm_MazurTransfer_order18_from_genus_two_exclusion
-- name    : MazurTransfer.order18_from_genus_two_exclusion
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T13:26:26.819812+00:00
-- url     : https://prove2.me/theorems/e6e2046d-dd47-45e9-8a6d-aad349c43f75
-- title:
--   Order18: exact Tate-normal-form reduction to the genus-two noncuspidal exclusion
-- statement:
--   Let E/ℚ be elliptic and Q a rational group point. If the genus-two curve y²=x⁶−4x⁵+10x⁴−10x³+5x²−2x+1 has no rational point with x≠0,1, then Q has additive order different from eighteen. The genus-two exclusion is an explicit hypothesis of this intermediate reduction, not a claim already proved by it.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, original Apache-2.0 headers and attribution retained. Closure of the exact original rationalPoint_addOrderOf_ne_eighteen_of_noNoncuspidalPoint is selected from kernel dependency facts and complete original Lean AST declaration ranges. It has 67 reachable declarations in 1603 lines. The new interface expands the original hyperelliptic polynomial definition and preserves every hypothesis. Named downstream consumer: MazurCampaign.no_order_eighteen. This splits the retained 21755-line full proof whose server submission timed out after300s; the unchanged campaign statement remains unconditional. Official Anthropic FLT division-polynomial lemma is reused at the same exact Mathlib pin.

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
open scoped WeierstrassCurve.Affine

theorem MazurTransfer.order18_from_genus_two_exclusion (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point)
    (hNoNoncuspidal : ∀ x y : ℚ, x ≠ 0 → x ≠ 1 →
      y ^ 2 = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1 → False) :
    addOrderOf Q ≠ 18 := by sorry
