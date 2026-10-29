-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p030_b024
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b024
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:05:50.947771+00:00
-- url     : https://prove2.me/theorems/c83aaa7b-1225-4d12-ad20-61495397691f
-- title:
--   Hlawka distinct profile 30, finite certificate block 25
-- statement:
--   For p in [95/16,6], the canonical charts whose indices lie in [53,54) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b024 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 53 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
