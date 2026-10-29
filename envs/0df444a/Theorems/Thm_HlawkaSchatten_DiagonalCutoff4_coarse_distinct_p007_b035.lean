-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b035
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b035
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:01:06.717201+00:00
-- url     : https://prove2.me/theorems/7b4c57f0-a0cd-4de5-9d15-264b062a8bf2
-- title:
--   Hlawka distinct profile 7, finite certificate block 36
-- statement:
--   For p in [135/32,17/4], the canonical charts whose indices lie in [73,78) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b035 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 73 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
