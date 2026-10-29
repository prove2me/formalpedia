-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p008_b082
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p008_b082
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:36:36.533928+00:00
-- url     : https://prove2.me/theorems/dd1447bf-b98a-49dd-af66-dc02f8ca1233
-- title:
--   Hlawka repeated profile 8, finite certificate block 83
-- statement:
--   For p in [5,41/8], the canonical charts whose indices lie in [246,249) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p008_b082 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 323) (hlo : 246 ≤ c.val) (hhi : c.val < 249)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
