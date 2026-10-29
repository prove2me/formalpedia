-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p017_b011
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b011
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:23:42.59915+00:00
-- url     : https://prove2.me/theorems/980a045f-8798-414a-844e-5d6ede3941e7
-- title:
--   Hlawka reusable ordered-chart block 25–26 for 77/16 ≤ p ≤ 79/16
-- statement:
--   For p in [77/16,79/16], the displayed normalized parameters exclude each canonical chart with index c in [25,27). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b011 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 27)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
