-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b018
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b018
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:24:48.320745+00:00
-- url     : https://prove2.me/theorems/7e0eae54-a5d2-4474-bbf0-0f7ddb26d8e7
-- title:
--   Reusable support-free repeated-chart block 54 to 56
-- statement:
--   For 9/2 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [54,57).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b018 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 54 ≤ c.val) (hhi : c.val < 57)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
