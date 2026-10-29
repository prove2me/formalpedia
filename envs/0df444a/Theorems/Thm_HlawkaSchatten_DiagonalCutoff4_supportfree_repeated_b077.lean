-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b077
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b077
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:30:45.77562+00:00
-- url     : https://prove2.me/theorems/e10d610b-c09e-4b17-9c70-a25acc988e71
-- title:
--   Reusable support-free repeated-chart block 231 to 233
-- statement:
--   For 39/8 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [231,234).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b077 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 231 ≤ c.val) (hhi : c.val < 234)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
