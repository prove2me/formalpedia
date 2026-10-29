-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b102
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b102
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:38:08.909865+00:00
-- url     : https://prove2.me/theorems/bed72085-0f71-4bdb-a971-e8e528585d3e
-- title:
--   Reusable support-free repeated-chart block 306 to 308
-- statement:
--   For 5 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [306,309).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b102 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 306 ≤ c.val) (hhi : c.val < 309)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
