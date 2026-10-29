-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b040
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b040
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:52:42.328979+00:00
-- url     : https://prove2.me/theorems/90c8496a-5a33-4591-9ea4-e73380efb105
-- title:
--   Hlawka repeated profile 3, finite certificate block 41
-- statement:
--   For p in [35/8,9/2], the canonical charts whose indices lie in [120,123) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b040 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 323) (hlo : 120 ≤ c.val) (hhi : c.val < 123)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
