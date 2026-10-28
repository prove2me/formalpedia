-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p001_b072
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b072
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:24:05.131248+00:00
-- url     : https://prove2.me/theorems/d3664d24-5b15-454e-bdb1-31cacaf9087f
-- title:
--   Hlawka repeated profile 1, finite certificate block 73
-- statement:
--   For p in [33/8,17/4], the canonical charts whose indices lie in [198,201) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b072 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 198 ≤ c.val) (hhi : c.val < 201)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
