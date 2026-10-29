-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b017
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b017
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:24:47.459518+00:00
-- url     : https://prove2.me/theorems/a29b09ec-0f15-4188-846d-2c1a71e9c18e
-- title:
--   Reusable support-free repeated-chart block 51 to 53
-- statement:
--   For 9/2 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [51,54).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b017 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 51 ≤ c.val) (hhi : c.val < 54)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
