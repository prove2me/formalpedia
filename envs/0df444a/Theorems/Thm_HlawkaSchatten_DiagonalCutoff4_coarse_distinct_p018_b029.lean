-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p018_b029
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b029
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:26:13.897712+00:00
-- url     : https://prove2.me/theorems/516d96ea-e00a-4719-879a-20a8189734d6
-- title:
--   Hlawka distinct profile 18, finite certificate block 30
-- statement:
--   For p in [39/8,79/16], the canonical charts whose indices lie in [65,68) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b029 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 65 ≤ c.val) (hhi : c.val < 68)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
