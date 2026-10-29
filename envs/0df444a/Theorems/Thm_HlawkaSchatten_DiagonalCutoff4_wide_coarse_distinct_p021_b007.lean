-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p021_b007
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p021_b007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:41:07.303495+00:00
-- url     : https://prove2.me/theorems/b5a9aa57-9c08-4027-900e-266a7f492af2
-- title:
--   Hlawka reusable ordered-chart block 17–18 for 81/16 ≤ p ≤ 83/16
-- statement:
--   For p in [81/16,83/16], the displayed normalized parameters exclude each canonical chart with index c in [17,19). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p021_b007 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 17 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
