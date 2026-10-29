-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b055
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b055
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:17:25.784994+00:00
-- url     : https://prove2.me/theorems/890a84df-2709-4406-a143-79566306223f
-- title:
--   Reusable support-free repeated-chart block 165 to 167
-- statement:
--   For 19/4 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [165,168).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b055 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 165 ≤ c.val) (hhi : c.val < 168)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
