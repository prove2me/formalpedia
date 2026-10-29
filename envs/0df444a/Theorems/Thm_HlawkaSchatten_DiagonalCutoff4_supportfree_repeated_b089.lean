-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b089
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b089
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:17:40.52099+00:00
-- url     : https://prove2.me/theorems/743d5203-ddc6-42f6-8823-f442227786de
-- title:
--   Reusable support-free repeated-chart block 267 to 269
-- statement:
--   For 19/4 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [267,270).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b089 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 267 ≤ c.val) (hhi : c.val < 270)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
