-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p020_b032
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p020_b032
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:35:53.592979+00:00
-- url     : https://prove2.me/theorems/517ae70b-cc4a-4615-925a-bc309e67659c
-- title:
--   Hlawka distinct profile 20, finite certificate block 33
-- statement:
--   For p in [5,81/16], the canonical charts whose indices lie in [57,58) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p020_b032 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
