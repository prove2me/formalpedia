-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b079
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b079
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:17:36.181422+00:00
-- url     : https://prove2.me/theorems/8853bda0-a0fc-4b10-9f24-0157f2b615fa
-- title:
--   Reusable support-free repeated-chart block 237 to 239
-- statement:
--   For 19/4 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [237,240).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b079 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 237 ≤ c.val) (hhi : c.val < 240)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
