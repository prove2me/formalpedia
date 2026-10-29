-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p008_b106
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p008_b106
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:36:36.885752+00:00
-- url     : https://prove2.me/theorems/e1aa25b4-7d7f-436d-875f-7c4ffc7e8da4
-- title:
--   Hlawka repeated profile 8, finite certificate block 107
-- statement:
--   For p in [5,41/8], the canonical charts whose indices lie in [318,321) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p008_b106 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 323) (hlo : 318 ≤ c.val) (hhi : c.val < 321)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
