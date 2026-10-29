-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p004_b075
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p004_b075
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:16:08.904341+00:00
-- url     : https://prove2.me/theorems/c0230da4-2186-4dd7-aaa3-c67528836edf
-- title:
--   Hlawka repeated profile 4, finite certificate block 76
-- statement:
--   For p in [9/2,37/8], the canonical charts whose indices lie in [225,228) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p004_b075 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 323) (hlo : 225 ≤ c.val) (hhi : c.val < 228)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
