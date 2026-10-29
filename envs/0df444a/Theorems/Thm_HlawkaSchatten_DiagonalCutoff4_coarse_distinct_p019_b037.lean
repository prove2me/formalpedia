-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p019_b037
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b037
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:33:16.290993+00:00
-- url     : https://prove2.me/theorems/e175fb9c-87c9-4509-a9e5-0a0dd791370f
-- title:
--   Hlawka distinct profile 19, finite certificate block 38
-- statement:
--   For p in [79/16,5], the canonical charts whose indices lie in [75,76) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b037 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 75 ≤ c.val) (hhi : c.val < 76)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
