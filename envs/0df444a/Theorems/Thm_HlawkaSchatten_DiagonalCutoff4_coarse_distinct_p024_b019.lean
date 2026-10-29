-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b019
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b019
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:48:13.96822+00:00
-- url     : https://prove2.me/theorems/28013c43-f154-494c-8624-5ecb996924e0
-- title:
--   Hlawka distinct profile 24, finite certificate block 20
-- statement:
--   For p in [21/4,85/16], the canonical charts whose indices lie in [39,41) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b019 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
