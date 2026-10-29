-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p021_b003
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p021_b003
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:39:30.009802+00:00
-- url     : https://prove2.me/theorems/fff2857c-16a8-4e01-9aaa-1aa4cfe60cc7
-- title:
--   Hlawka distinct profile 21, finite certificate block 4
-- statement:
--   For p in [81/16,41/8], the canonical charts whose indices lie in [8,10) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p021_b003 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 8 ≤ c.val) (hhi : c.val < 10)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
