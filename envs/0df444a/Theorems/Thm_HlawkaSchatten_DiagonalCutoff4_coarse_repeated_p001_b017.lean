-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p001_b017
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b017
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:20:49.766842+00:00
-- url     : https://prove2.me/theorems/765bb1d8-3133-4f3f-9038-de6d0d1953c8
-- title:
--   Hlawka repeated profile 1, finite certificate block 18
-- statement:
--   For p in [33/8,17/4], the canonical charts whose indices lie in [51,54) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b017 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 51 ≤ c.val) (hhi : c.val < 54)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
