-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b060
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b060
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:43:29.588949+00:00
-- url     : https://prove2.me/theorems/48cc9361-3791-4649-94a5-7d8481443ea3
-- title:
--   Reusable support-free repeated-chart block 180 to 182
-- statement:
--   For 41/8 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [180,183).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b060 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 180 ≤ c.val) (hhi : c.val < 183)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
