-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b066
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b066
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:00:04.353486+00:00
-- url     : https://prove2.me/theorems/42c59791-6cc4-4c01-8a6f-c930c3517624
-- title:
--   Reusable support-free repeated-chart block 198 to 200
-- statement:
--   For 35/8 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [198,201).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b066 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 198 ≤ c.val) (hhi : c.val < 201)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
