-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p001_b075
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b075
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:24:08.505401+00:00
-- url     : https://prove2.me/theorems/04c188ae-0fdd-4077-bf53-3712dcee56d0
-- title:
--   Hlawka repeated profile 1, finite certificate block 76
-- statement:
--   For p in [33/8,17/4], the canonical charts whose indices lie in [207,210) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b075 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 207 ≤ c.val) (hhi : c.val < 210)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
