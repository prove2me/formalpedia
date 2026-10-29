-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p014_b018
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b018
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:03:18.804996+00:00
-- url     : https://prove2.me/theorems/fd67df8e-c35e-4edd-bca9-ad7af19c2229
-- title:
--   Hlawka reusable ordered-chart block 37–37 for 37/8 ≤ p ≤ 19/4
-- statement:
--   For p in [37/8,19/4], the displayed normalized parameters exclude each canonical chart with index c in [37,38). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b018 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
