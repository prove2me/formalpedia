-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p009_b032
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b032
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:39:49.036199+00:00
-- url     : https://prove2.me/theorems/55acb66d-1eee-4363-a1d9-31f9602adb8e
-- title:
--   Hlawka distinct profile 9, finite certificate block 33
-- statement:
--   For p in [69/16,35/8], the canonical charts whose indices lie in [70,71) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b032 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
