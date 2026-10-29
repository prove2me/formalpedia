-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p009_b035
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b035
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:40:03.699262+00:00
-- url     : https://prove2.me/theorems/bfd695e0-f781-44ec-91aa-f2065621ac7a
-- title:
--   Hlawka distinct profile 9, finite certificate block 36
-- statement:
--   For p in [69/16,35/8], the canonical charts whose indices lie in [77,79) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b035 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 79)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
