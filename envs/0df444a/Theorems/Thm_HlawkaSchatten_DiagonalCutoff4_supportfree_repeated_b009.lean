-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b009
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b009
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:27:03.62065+00:00
-- url     : https://prove2.me/theorems/7b021cf9-1b56-42c0-8957-acdd0a7f4bfd
-- title:
--   Reusable support-free repeated-chart block 27 to 29
-- statement:
--   For 17/4 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [27,30).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b009 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 27 ≤ c.val) (hhi : c.val < 30)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
