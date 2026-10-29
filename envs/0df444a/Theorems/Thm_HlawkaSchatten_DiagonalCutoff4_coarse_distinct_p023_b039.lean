-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p023_b039
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p023_b039
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:45:45.329065+00:00
-- url     : https://prove2.me/theorems/14853dad-1fe1-45e8-aa11-36a65e37bf0c
-- title:
--   Hlawka distinct profile 23, finite certificate block 40
-- statement:
--   For p in [83/16,21/4], the canonical charts whose indices lie in [72,75) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p023_b039 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 72 ≤ c.val) (hhi : c.val < 75)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
