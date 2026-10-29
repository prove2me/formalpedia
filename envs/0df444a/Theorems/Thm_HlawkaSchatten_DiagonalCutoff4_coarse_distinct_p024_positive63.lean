-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_positive63
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_positive63
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:48:58.167492+00:00
-- url     : https://prove2.me/theorems/9dbcb953-0f10-47ac-98b0-a15fd4e3713f
-- title:
--   Hlawka positive chart 63, profile 24, has tails at most two fifths
-- statement:
--   For p in [21/4,85/16], the displayed canonical positive ordered chart has every off-main pair coordinate bounded by two fifths of its main coordinate.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_positive63 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders 63) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by sorry
