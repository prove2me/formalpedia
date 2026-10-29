-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p029_b023
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b023
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:02:51.554086+00:00
-- url     : https://prove2.me/theorems/4c3a2572-e7c3-4b0b-8eaf-f989154a866d
-- title:
--   Hlawka distinct profile 29, finite certificate block 24
-- statement:
--   For p in [93/16,95/16], the canonical charts whose indices lie in [50,51) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b023 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 50 ≤ c.val) (hhi : c.val < 51)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
