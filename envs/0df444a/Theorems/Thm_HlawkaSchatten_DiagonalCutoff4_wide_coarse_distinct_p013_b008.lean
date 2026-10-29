-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p013_b008
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p013_b008
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:54:10.703032+00:00
-- url     : https://prove2.me/theorems/2d29d9d2-8267-48f0-9d84-1b02123e5dd0
-- title:
--   Hlawka reusable ordered-chart block 17–18 for 73/16 ≤ p ≤ 75/16
-- statement:
--   For p in [73/16,75/16], the displayed normalized parameters exclude each canonical chart with index c in [17,19). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p013_b008 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 17 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
