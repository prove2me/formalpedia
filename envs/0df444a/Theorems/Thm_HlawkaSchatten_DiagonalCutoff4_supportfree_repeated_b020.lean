-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b020
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b020
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:24:59.862239+00:00
-- url     : https://prove2.me/theorems/018812d0-6dae-4d1b-8c3e-b522333b4ea1
-- title:
--   Reusable support-free repeated-chart block 60 to 62
-- statement:
--   For 9/2 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [60,63).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b020 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 60 ≤ c.val) (hhi : c.val < 63)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
