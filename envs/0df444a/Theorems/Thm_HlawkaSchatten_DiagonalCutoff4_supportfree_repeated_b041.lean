-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b041
-- name    : HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b041
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:02:30.535992+00:00
-- url     : https://prove2.me/theorems/af10ea1e-3c48-4f05-a638-bdcaa654c5d5
-- title:
--   Reusable support-free repeated-chart block 123 to 125
-- statement:
--   For 37/8 ≤ p ≤ 6, the displayed ordered-chart parameters exclude each repeated canonical chart in [123,126).
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.supportfree_repeated_b041 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ 6)
    (c : Fin 323) (hlo : 123 ≤ c.val) (hhi : c.val < 126)
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
