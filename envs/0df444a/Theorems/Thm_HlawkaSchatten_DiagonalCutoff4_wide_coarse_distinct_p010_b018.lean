-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b018
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b018
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:01:02.305816+00:00
-- url     : https://prove2.me/theorems/f62d6492-d1e1-4f69-95e9-5f57081ea40d
-- title:
--   Hlawka reusable ordered-chart block 30–31 for 35/8 ≤ p ≤ 9/2
-- statement:
--   For p in [35/8,9/2], the displayed normalized parameters exclude each canonical chart with index c in [30,32). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b018 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
