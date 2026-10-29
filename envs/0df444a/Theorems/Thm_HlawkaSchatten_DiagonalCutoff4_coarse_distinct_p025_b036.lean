-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p025_b036
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b036
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:51:34.286577+00:00
-- url     : https://prove2.me/theorems/a25bf5fd-5342-41e7-90b0-32e5a2165830
-- title:
--   Hlawka distinct profile 25, finite certificate block 37
-- statement:
--   For p in [85/16,87/16], the canonical charts whose indices lie in [70,72) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b036 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
