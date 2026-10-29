-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p026_b039
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b039
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:54:55.302342+00:00
-- url     : https://prove2.me/theorems/e1500591-c261-4e0a-81e5-e2b244a941fe
-- title:
--   Hlawka distinct profile 26, finite certificate block 40
-- statement:
--   For p in [87/16,89/16], the canonical charts whose indices lie in [78,80) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b039 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 80)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
