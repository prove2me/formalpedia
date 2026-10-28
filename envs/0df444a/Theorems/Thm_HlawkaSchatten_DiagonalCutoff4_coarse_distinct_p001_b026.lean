-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p001_b026
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b026
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:22:14.855304+00:00
-- url     : https://prove2.me/theorems/bb7b68f8-b232-47fa-b47b-16531186092b
-- title:
--   Hlawka distinct profile 1, finite certificate block 27
-- statement:
--   For p in [129/32,65/16], the canonical charts whose indices lie in [46,54) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b026 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
