-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p012_b026
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p012_b026
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:14:29.987463+00:00
-- url     : https://prove2.me/theorems/f78d5499-ce9c-435c-96e0-c05c17ea31f6
-- title:
--   Hlawka distinct profile 12, finite certificate block 27
-- statement:
--   For p in [9/2,73/16], the canonical charts whose indices lie in [66,68) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p012_b026 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 66 ≤ c.val) (hhi : c.val < 68)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
