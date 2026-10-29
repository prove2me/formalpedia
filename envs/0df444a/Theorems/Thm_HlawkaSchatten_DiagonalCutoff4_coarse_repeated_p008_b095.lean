-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p008_b095
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p008_b095
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:36:35.766111+00:00
-- url     : https://prove2.me/theorems/8ee5d7ab-d13c-4a20-a72d-3583c053219a
-- title:
--   Hlawka repeated profile 8, finite certificate block 96
-- statement:
--   For p in [5,41/8], the canonical charts whose indices lie in [285,288) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p008_b095 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 323) (hlo : 285 ≤ c.val) (hhi : c.val < 288)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
