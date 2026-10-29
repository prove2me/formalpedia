-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p006_b035
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p006_b035
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:34:43.389327+00:00
-- url     : https://prove2.me/theorems/ba6d239c-fecf-4f2e-bf38-ce27a2ac6212
-- title:
--   Hlawka distinct profile 6, finite certificate block 36
-- statement:
--   For p in [67/16,135/32], the canonical charts whose indices lie in [79,81) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p006_b035 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
