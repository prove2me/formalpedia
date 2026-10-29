-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p028_b022
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b022
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:59:49.2932+00:00
-- url     : https://prove2.me/theorems/168e66d2-29ce-44b7-9393-eeaa8f2b69f3
-- title:
--   Hlawka distinct profile 28, finite certificate block 23
-- statement:
--   For p in [91/16,93/16], the canonical charts whose indices lie in [49,50) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b022 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 49 ≤ c.val) (hhi : c.val < 50)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
