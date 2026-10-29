-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p009_b028
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b028
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:39:47.854957+00:00
-- url     : https://prove2.me/theorems/64efd076-2fc3-4d65-ac8b-c6fe2611eb03
-- title:
--   Hlawka distinct profile 9, finite certificate block 29
-- statement:
--   For p in [69/16,35/8], the canonical charts whose indices lie in [62,66) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b028 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
