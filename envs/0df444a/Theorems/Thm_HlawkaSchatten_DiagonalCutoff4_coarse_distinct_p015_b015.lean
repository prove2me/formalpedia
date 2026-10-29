-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p015_b015
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b015
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:05:52.213765+00:00
-- url     : https://prove2.me/theorems/a3a03b45-51f9-4283-b547-5a848812be79
-- title:
--   Hlawka distinct profile 15, finite certificate block 16
-- statement:
--   For p in [75/16,19/4], the canonical charts whose indices lie in [30,33) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b015 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 33)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
