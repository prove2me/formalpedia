-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p015_b012
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p015_b012
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:08:58.518693+00:00
-- url     : https://prove2.me/theorems/3fda6bf1-9c2a-431c-9878-ada008df04a2
-- title:
--   Hlawka reusable ordered-chart block 25–26 for 75/16 ≤ p ≤ 77/16
-- statement:
--   For p in [75/16,77/16], the displayed normalized parameters exclude each canonical chart with index c in [25,27). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p015_b012 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 27)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
