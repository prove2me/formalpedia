-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b084
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b084
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:54:18.056154+00:00
-- url     : https://prove2.me/theorems/cf416d28-3db7-4b1c-9445-b4cd4e177991
-- title:
--   Hlawka repeated profile 3, finite certificate block 85
-- statement:
--   For p in [35/8,9/2], the canonical charts whose indices lie in [252,255) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b084 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 323) (hlo : 252 ≤ c.val) (hhi : c.val < 255)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
