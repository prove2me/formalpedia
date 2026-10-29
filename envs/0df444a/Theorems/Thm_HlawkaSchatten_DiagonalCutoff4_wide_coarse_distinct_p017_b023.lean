-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p017_b023
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b023
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:23:50.94393+00:00
-- url     : https://prove2.me/theorems/f12ea9ef-d543-4e01-90c8-b93d0124937a
-- title:
--   Hlawka reusable ordered-chart block 48–48 for 77/16 ≤ p ≤ 79/16
-- statement:
--   For p in [77/16,79/16], the displayed normalized parameters exclude each canonical chart with index c in [48,49). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b023 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 48 ≤ c.val) (hhi : c.val < 49)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
