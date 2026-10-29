-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b023
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b023
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:25:03.639588+00:00
-- url     : https://prove2.me/theorems/bf7827e8-b63f-4941-9930-c30eba678b64
-- title:
--   Reusable support-free repeated-chart block 69 to 71
-- statement:
--   For 9/2 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [69,72).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b023 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 69 ≤ c.val) (hhi : c.val < 72)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
