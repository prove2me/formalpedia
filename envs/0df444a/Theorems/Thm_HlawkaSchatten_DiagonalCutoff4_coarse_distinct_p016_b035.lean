-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p016_b035
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b035
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:11:55.147822+00:00
-- url     : https://prove2.me/theorems/d364dbf0-191b-4364-b97c-c416adaa929e
-- title:
--   Hlawka distinct profile 16, finite certificate block 36
-- statement:
--   For p in [19/4,77/16], the canonical charts whose indices lie in [85,88) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b035 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
