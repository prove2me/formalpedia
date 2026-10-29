-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p013_b031
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b031
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:51:34.265707+00:00
-- url     : https://prove2.me/theorems/3749c00e-5ebe-4a0b-8ab1-5ea648780ac8
-- title:
--   Hlawka distinct profile 13, finite certificate block 32
-- statement:
--   For p in [73/16,37/8], the canonical charts whose indices lie in [78,81) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b031 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
