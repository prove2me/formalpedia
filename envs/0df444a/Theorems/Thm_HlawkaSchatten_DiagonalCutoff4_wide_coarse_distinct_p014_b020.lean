-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p014_b020
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b020
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:03:15.630735+00:00
-- url     : https://prove2.me/theorems/423f1bea-3421-4879-896b-e5dfa73f2df8
-- title:
--   Hlawka reusable ordered-chart block 39–40 for 37/8 ≤ p ≤ 19/4
-- statement:
--   For p in [37/8,19/4], the displayed normalized parameters exclude each canonical chart with index c in [39,41). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b020 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
