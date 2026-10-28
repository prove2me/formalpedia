-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p001_b045
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b045
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:22:19.547118+00:00
-- url     : https://prove2.me/theorems/851386d0-d1e7-41af-ad21-700eb2e3e594
-- title:
--   Hlawka repeated profile 1, finite certificate block 46
-- statement:
--   For p in [33/8,17/4], the canonical charts whose indices lie in [130,133) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b045 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 130 ≤ c.val) (hhi : c.val < 133)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
