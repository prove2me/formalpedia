-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p018_b022
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b022
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:31:20.103982+00:00
-- url     : https://prove2.me/theorems/a58f755a-7ce1-4bed-875d-852f96a9bfd3
-- title:
--   Hlawka reusable ordered-chart block 46–46 for 39/8 ≤ p ≤ 5
-- statement:
--   For p in [39/8,5], the displayed normalized parameters exclude each canonical chart with index c in [46,47). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b022 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
