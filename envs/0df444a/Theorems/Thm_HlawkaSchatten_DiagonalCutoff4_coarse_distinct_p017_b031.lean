-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p017_b031
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b031
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:20:58.240508+00:00
-- url     : https://prove2.me/theorems/501e4f43-18fe-4cb3-9114-f160c5c60969
-- title:
--   Hlawka distinct profile 17, finite certificate block 32
-- statement:
--   For p in [77/16,39/8], the canonical charts whose indices lie in [72,75) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b031 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 72 ≤ c.val) (hhi : c.val < 75)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
