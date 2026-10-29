-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b057
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b057
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:03:07.140527+00:00
-- url     : https://prove2.me/theorems/a97e6ecb-424d-455b-9cad-a3b40196db43
-- title:
--   Reusable support-free repeated-chart block 171 to 173
-- statement:
--   For 37/8 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [171,174).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b057 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 171 ≤ c.val) (hhi : c.val < 174)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
