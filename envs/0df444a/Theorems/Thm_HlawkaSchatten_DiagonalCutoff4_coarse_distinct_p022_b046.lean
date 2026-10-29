-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p022_b046
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b046
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:42:28.884221+00:00
-- url     : https://prove2.me/theorems/1b9f6538-34d6-419f-a5ef-ea866bd0a61f
-- title:
--   Hlawka distinct profile 22, finite certificate block 47
-- statement:
--   For p in [41/8,83/16], the canonical charts whose indices lie in [85,88) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b046 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
