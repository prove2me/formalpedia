-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p005_b054
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p005_b054
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:57:51.481531+00:00
-- url     : https://prove2.me/theorems/9a50d77a-b389-4dcc-9475-68d421702071
-- title:
--   Hlawka repeated profile 5, finite certificate block 55
-- statement:
--   For p in [37/8,19/4], the canonical charts whose indices lie in [162,165) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p005_b054 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 323) (hlo : 162 ≤ c.val) (hhi : c.val < 165)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
