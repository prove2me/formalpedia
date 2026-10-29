-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b031
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b031
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:51:51.72428+00:00
-- url     : https://prove2.me/theorems/729d215d-6261-4ea7-b7a4-aa0d53453573
-- title:
--   Hlawka distinct profile 10, finite certificate block 32
-- statement:
--   For p in [35/8,71/16], the canonical charts whose indices lie in [69,71) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b031 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
