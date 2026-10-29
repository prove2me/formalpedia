-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p025_b021
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b021
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:51:01.455785+00:00
-- url     : https://prove2.me/theorems/ae61ad14-30a7-486a-ac50-a7f1054551c7
-- title:
--   Hlawka distinct profile 25, finite certificate block 22
-- statement:
--   For p in [85/16,87/16], the canonical charts whose indices lie in [44,45) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b021 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 45)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
