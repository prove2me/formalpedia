-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b024
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p004_b024
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:39:41.693345+00:00
-- url     : https://prove2.me/theorems/a12f0e4f-d902-421b-be57-c28648a60458
-- title:
--   Hlawka reusable ordered-chart block 44–45 for 33/8 ≤ p ≤ 17/4
-- statement:
--   For p in [33/8,17/4], the displayed normalized parameters exclude each canonical chart with index c in [44,46). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p004_b024 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
