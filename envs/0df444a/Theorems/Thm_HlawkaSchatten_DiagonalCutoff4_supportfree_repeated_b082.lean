-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b082
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b082
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:49:41.724671+00:00
-- url     : https://prove2.me/theorems/e3fa4a75-aabf-461b-922b-cc40449aa3f4
-- title:
--   Reusable support-free repeated-chart block 246 to 248
-- statement:
--   For 21/4 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [246,249).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b082 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 246 ≤ c.val) (hhi : c.val < 249)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
