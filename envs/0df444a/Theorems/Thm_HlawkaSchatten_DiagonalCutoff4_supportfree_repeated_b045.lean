-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b045
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b045
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:00:03.829127+00:00
-- url     : https://prove2.me/theorems/61deb1ce-cd38-4253-8273-4e16efc293bd
-- title:
--   Reusable support-free repeated-chart block 135 to 137
-- statement:
--   For 35/8 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [135,138).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b045 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 135 ≤ c.val) (hhi : c.val < 138)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
