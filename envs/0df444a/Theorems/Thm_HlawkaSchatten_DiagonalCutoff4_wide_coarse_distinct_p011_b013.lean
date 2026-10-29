-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p011_b013
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p011_b013
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:09:20.09782+00:00
-- url     : https://prove2.me/theorems/bc2509ec-520f-4abd-90ed-e1a0acf8c4d3
-- title:
--   Hlawka reusable ordered-chart block 25–26 for 71/16 ≤ p ≤ 73/16
-- statement:
--   For p in [71/16,73/16], the displayed normalized parameters exclude each canonical chart with index c in [25,27). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p011_b013 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 27)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
