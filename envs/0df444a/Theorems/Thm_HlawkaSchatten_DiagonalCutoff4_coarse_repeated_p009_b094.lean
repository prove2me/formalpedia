-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p009_b094
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p009_b094
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:42:34.109221+00:00
-- url     : https://prove2.me/theorems/cf863d4f-5c71-432a-b2e1-be3410307d23
-- title:
--   Hlawka repeated profile 9, finite certificate block 95
-- statement:
--   For p in [41/8,21/4], the canonical charts whose indices lie in [282,285) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p009_b094 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 323) (hlo : 282 ≤ c.val) (hhi : c.val < 285)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
