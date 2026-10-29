-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p020_b042
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p020_b042
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:36:13.80311+00:00
-- url     : https://prove2.me/theorems/db957c2a-a166-4a2f-acae-7a69de3fdf88
-- title:
--   Hlawka distinct profile 20, finite certificate block 43
-- statement:
--   For p in [5,81/16], the canonical charts whose indices lie in [80,82) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p020_b042 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 80 ≤ c.val) (hhi : c.val < 82)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
