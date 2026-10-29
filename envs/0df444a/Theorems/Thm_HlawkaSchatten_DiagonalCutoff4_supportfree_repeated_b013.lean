-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b013
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b013
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:27:10.304374+00:00
-- url     : https://prove2.me/theorems/0e5ca0e8-c392-45a5-8e97-2b7d4f435a3b
-- title:
--   Reusable support-free repeated-chart block 39 to 41
-- statement:
--   For 17/4 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [39,42).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b013 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 39 ≤ c.val) (hhi : c.val < 42)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
