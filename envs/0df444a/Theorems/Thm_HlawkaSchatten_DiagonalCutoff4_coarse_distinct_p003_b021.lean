-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b021
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b021
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:52:37.908514+00:00
-- url     : https://prove2.me/theorems/d7a3494c-dacd-40d7-94b9-c2dea3b67b69
-- title:
--   Hlawka distinct profile 3, finite certificate block 22
-- statement:
--   For p in [131/32,33/8], the canonical charts whose indices lie in [41,43) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b021 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 43)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
