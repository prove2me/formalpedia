-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p007_b007
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p007_b007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:06:19.029901+00:00
-- url     : https://prove2.me/theorems/cf50833d-9d54-4550-89de-090356bde5a5
-- title:
--   Hlawka reusable ordered-chart block 15–16 for 135/32 ≤ p ≤ 139/32
-- statement:
--   For p in [135/32,139/32], the displayed normalized parameters exclude each canonical chart with index c in [15,17). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p007_b007 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (139/32 : ℝ))
    (c : Fin 88) (hlo : 15 ≤ c.val) (hhi : c.val < 17)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
