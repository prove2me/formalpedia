-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b005
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b005
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:26:52.157618+00:00
-- url     : https://prove2.me/theorems/fddbe59c-e69d-461c-9960-d3c12a61d38b
-- title:
--   Reusable support-free repeated-chart block 15 to 17
-- statement:
--   For 17/4 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [15,18).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b005 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 15 ≤ c.val) (hhi : c.val < 18)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
