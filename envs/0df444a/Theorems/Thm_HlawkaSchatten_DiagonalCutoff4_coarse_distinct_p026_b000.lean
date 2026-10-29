-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p026_b000
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b000
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:53:43.46738+00:00
-- url     : https://prove2.me/theorems/1621e7b7-9020-4d4b-979f-644cbe57c9b9
-- title:
--   Hlawka distinct profile 26, finite certificate block 1
-- statement:
--   For p in [87/16,89/16], the canonical charts whose indices lie in [0,3) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b000 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 0 ≤ c.val) (hhi : c.val < 3)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
