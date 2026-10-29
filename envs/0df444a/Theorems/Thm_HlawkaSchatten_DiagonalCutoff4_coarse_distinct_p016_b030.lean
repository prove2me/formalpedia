-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p016_b030
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b030
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:11:40.981841+00:00
-- url     : https://prove2.me/theorems/f8987a83-538a-44c0-b12e-8ed122051ccb
-- title:
--   Hlawka distinct profile 16, finite certificate block 31
-- statement:
--   For p in [19/4,77/16], the canonical charts whose indices lie in [72,76) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b030 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 72 ≤ c.val) (hhi : c.val < 76)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
