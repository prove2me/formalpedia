-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b070
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b070
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:30:46.927357+00:00
-- url     : https://prove2.me/theorems/7d392b6e-43c5-43d8-b34c-2bf0826f4f7f
-- title:
--   Reusable support-free repeated-chart block 210 to 212
-- statement:
--   For 39/8 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [210,213).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b070 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 210 ≤ c.val) (hhi : c.val < 213)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
