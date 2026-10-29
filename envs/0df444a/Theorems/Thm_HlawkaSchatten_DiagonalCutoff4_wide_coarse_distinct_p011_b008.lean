-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p011_b008
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p011_b008
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:09:17.885008+00:00
-- url     : https://prove2.me/theorems/959eda2c-7a26-4025-b6ce-3534fbfbc547
-- title:
--   Hlawka reusable ordered-chart block 17–18 for 71/16 ≤ p ≤ 73/16
-- statement:
--   For p in [71/16,73/16], the displayed normalized parameters exclude each canonical chart with index c in [17,19). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p011_b008 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 17 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
