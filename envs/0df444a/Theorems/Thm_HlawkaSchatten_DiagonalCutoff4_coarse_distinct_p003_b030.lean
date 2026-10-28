-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b030
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b030
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:52:45.868528+00:00
-- url     : https://prove2.me/theorems/178c5b20-6afa-4122-abed-bb5c31546738
-- title:
--   Hlawka distinct profile 3, finite certificate block 31
-- statement:
--   For p in [131/32,33/8], the canonical charts whose indices lie in [70,71) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b030 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
