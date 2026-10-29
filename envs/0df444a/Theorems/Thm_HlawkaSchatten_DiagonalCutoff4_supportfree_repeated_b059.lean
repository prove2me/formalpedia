-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b059
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b059
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:43:30.789039+00:00
-- url     : https://prove2.me/theorems/7d91d09d-0fa3-47d3-9e94-b74016149f38
-- title:
--   Reusable support-free repeated-chart block 177 to 179
-- statement:
--   For 41/8 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [177,180).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b059 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 177 ≤ c.val) (hhi : c.val < 180)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
