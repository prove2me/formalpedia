-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p013_b034
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b034
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:51:38.727651+00:00
-- url     : https://prove2.me/theorems/cbd58c9b-7d2b-4a7a-b759-6e776fd3ba58
-- title:
--   Hlawka distinct profile 13, finite certificate block 35
-- statement:
--   For p in [73/16,37/8], the canonical charts whose indices lie in [85,88) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b034 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
