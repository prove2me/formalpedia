-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p014_positive87
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_positive87
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:57:08.225599+00:00
-- url     : https://prove2.me/theorems/81c5a9a4-06c1-4f79-a1ee-ba48f530f25c
-- title:
--   Hlawka positive chart 87, profile 14, has tails at most two fifths
-- statement:
--   For p in [37/8,75/16], the displayed canonical positive ordered chart has every off-main pair coordinate bounded by two fifths of its main coordinate.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_positive87 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by sorry
