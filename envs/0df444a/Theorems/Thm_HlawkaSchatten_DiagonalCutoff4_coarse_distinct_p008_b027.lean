-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p008_b027
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b027
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:16:04.925647+00:00
-- url     : https://prove2.me/theorems/3ab87f11-a674-4853-b220-0fe22f5dd0d8
-- title:
--   Hlawka distinct profile 8, finite certificate block 28
-- statement:
--   For p in [17/4,69/16], the canonical charts whose indices lie in [46,54) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b027 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
