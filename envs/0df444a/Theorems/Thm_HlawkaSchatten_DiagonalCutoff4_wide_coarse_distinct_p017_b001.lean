-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p017_b001
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b001
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:23:31.309446+00:00
-- url     : https://prove2.me/theorems/b4b8b5d8-21fe-465b-bca3-06dcbae06b9d
-- title:
--   Hlawka reusable ordered-chart block 3–5 for 77/16 ≤ p ≤ 79/16
-- statement:
--   For p in [77/16,79/16], the displayed normalized parameters exclude each canonical chart with index c in [3,6). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b001 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 3 ≤ c.val) (hhi : c.val < 6)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
