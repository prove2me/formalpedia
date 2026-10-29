-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p028_b028
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b028
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:00:27.242079+00:00
-- url     : https://prove2.me/theorems/57893d8c-1d43-4ef7-9463-2b5e3e5871a4
-- title:
--   Hlawka distinct profile 28, finite certificate block 29
-- statement:
--   For p in [91/16,93/16], the canonical charts whose indices lie in [58,59) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b028 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 58 ≤ c.val) (hhi : c.val < 59)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
