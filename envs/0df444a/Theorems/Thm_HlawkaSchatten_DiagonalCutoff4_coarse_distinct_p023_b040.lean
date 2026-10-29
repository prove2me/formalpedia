-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p023_b040
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p023_b040
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:45:46.205604+00:00
-- url     : https://prove2.me/theorems/e3ebfdf9-52ef-4e9f-9e23-e7646ead95ef
-- title:
--   Hlawka distinct profile 23, finite certificate block 41
-- statement:
--   For p in [83/16,21/4], the canonical charts whose indices lie in [75,76) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p023_b040 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 75 ≤ c.val) (hhi : c.val < 76)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
