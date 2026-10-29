-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p014_b027
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b027
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:56:26.130971+00:00
-- url     : https://prove2.me/theorems/5be7c6d1-9df0-4fa6-9e40-0c2a9bfb7bb7
-- title:
--   Hlawka distinct profile 14, finite certificate block 28
-- statement:
--   For p in [37/8,75/16], the canonical charts whose indices lie in [66,68) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b027 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 66 ≤ c.val) (hhi : c.val < 68)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
