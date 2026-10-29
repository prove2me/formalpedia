-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p005_b035
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b035
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:55:29.802808+00:00
-- url     : https://prove2.me/theorems/0f418373-a6ea-4ded-9ce7-98e9db0b8876
-- title:
--   Hlawka distinct profile 5, finite certificate block 36
-- statement:
--   For p in [133/32,67/16], the canonical charts whose indices lie in [79,81) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b035 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
