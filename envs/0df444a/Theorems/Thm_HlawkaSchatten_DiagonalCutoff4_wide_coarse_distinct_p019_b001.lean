-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p019_b001
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b001
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:34:43.466919+00:00
-- url     : https://prove2.me/theorems/5ad4a415-5b76-496e-98e2-7d1f7ba76bc4
-- title:
--   Hlawka reusable ordered-chart block 3–5 for 79/16 ≤ p ≤ 81/16
-- statement:
--   For p in [79/16,81/16], the displayed normalized parameters exclude each canonical chart with index c in [3,6). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b001 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 3 ≤ c.val) (hhi : c.val < 6)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
