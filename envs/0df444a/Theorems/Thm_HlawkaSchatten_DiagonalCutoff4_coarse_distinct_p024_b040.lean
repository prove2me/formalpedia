-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b040
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b040
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:48:25.495106+00:00
-- url     : https://prove2.me/theorems/a23ba43a-6e87-4d1e-8986-3b1179776f76
-- title:
--   Hlawka distinct profile 24, finite certificate block 41
-- statement:
--   For p in [21/4,85/16], the canonical charts whose indices lie in [78,80) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b040 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 80)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
