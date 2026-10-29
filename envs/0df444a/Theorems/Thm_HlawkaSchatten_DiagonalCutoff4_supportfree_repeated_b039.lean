-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b039
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b039
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:37:48.331858+00:00
-- url     : https://prove2.me/theorems/e1245aea-cfe3-41ea-b7c0-62e8bbb4b202
-- title:
--   Reusable support-free repeated-chart block 117 to 119
-- statement:
--   For 5 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [117,120).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b039 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 117 ≤ c.val) (hhi : c.val < 120)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
