-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b062
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b062
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:53:40.771044+00:00
-- url     : https://prove2.me/theorems/25b1c98f-863d-4fe6-8a64-d8f41e3d301d
-- title:
--   Hlawka repeated profile 3, finite certificate block 63
-- statement:
--   For p in [35/8,9/2], the canonical charts whose indices lie in [186,189) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b062 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 323) (hlo : 186 ≤ c.val) (hhi : c.val < 189)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
