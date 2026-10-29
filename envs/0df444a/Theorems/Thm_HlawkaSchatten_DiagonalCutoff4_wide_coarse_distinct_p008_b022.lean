-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p008_b022
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b022
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:28:31.44145+00:00
-- url     : https://prove2.me/theorems/3f79b8dc-a811-42f7-9b15-1cfc0bdee16c
-- title:
--   Hlawka reusable ordered-chart block 37–37 for 17/4 ≤ p ≤ 35/8
-- statement:
--   For p in [17/4,35/8], the displayed normalized parameters exclude each canonical chart with index c in [37,38). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b022 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
