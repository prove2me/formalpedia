-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p017_b002
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b002
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:23:36.200407+00:00
-- url     : https://prove2.me/theorems/fed2d678-9db2-4771-94b4-62b9ae0febe5
-- title:
--   Hlawka reusable ordered-chart block 6–7 for 77/16 ≤ p ≤ 79/16
-- statement:
--   For p in [77/16,79/16], the displayed normalized parameters exclude each canonical chart with index c in [6,8). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b002 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 6 ≤ c.val) (hhi : c.val < 8)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
