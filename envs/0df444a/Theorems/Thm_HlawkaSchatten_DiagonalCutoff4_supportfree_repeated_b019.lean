-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b019
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b019
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:27:24.099297+00:00
-- url     : https://prove2.me/theorems/960a06ac-bd6f-41b0-ac54-91dbe64e4acc
-- title:
--   Reusable support-free repeated-chart block 57 to 59
-- statement:
--   For 17/4 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [57,60).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b019 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 57 ≤ c.val) (hhi : c.val < 60)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
