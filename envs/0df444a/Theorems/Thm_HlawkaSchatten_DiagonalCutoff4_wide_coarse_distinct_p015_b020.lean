-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p015_b020
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p015_b020
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:09:00.051592+00:00
-- url     : https://prove2.me/theorems/fb215edd-f715-411e-909b-cd9a89ebdec9
-- title:
--   Hlawka reusable ordered-chart block 41–43 for 75/16 ≤ p ≤ 77/16
-- statement:
--   For p in [75/16,77/16], the displayed normalized parameters exclude each canonical chart with index c in [41,44). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p015_b020 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 44)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
