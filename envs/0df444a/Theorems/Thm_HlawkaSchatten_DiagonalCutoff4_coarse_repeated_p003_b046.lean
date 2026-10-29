-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b046
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b046
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:53:26.167032+00:00
-- url     : https://prove2.me/theorems/548f1f6b-955b-4b7e-ba4c-8eceb4c0169c
-- title:
--   Hlawka repeated profile 3, finite certificate block 47
-- statement:
--   For p in [35/8,9/2], the canonical charts whose indices lie in [138,141) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b046 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 323) (hlo : 138 ≤ c.val) (hhi : c.val < 141)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
