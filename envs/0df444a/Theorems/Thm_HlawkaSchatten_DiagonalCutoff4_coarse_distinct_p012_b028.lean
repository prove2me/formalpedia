-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p012_b028
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p012_b028
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:14:27.914531+00:00
-- url     : https://prove2.me/theorems/b928b129-b3da-40ee-9c63-3b8603a972fc
-- title:
--   Hlawka distinct profile 12, finite certificate block 29
-- statement:
--   For p in [9/2,73/16], the canonical charts whose indices lie in [69,71) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p012_b028 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
