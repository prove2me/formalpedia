-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p027_b027
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b027
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:57:27.97198+00:00
-- url     : https://prove2.me/theorems/06a22b87-c232-465b-96d7-3bfa5375c100
-- title:
--   Hlawka distinct profile 27, finite certificate block 28
-- statement:
--   For p in [89/16,91/16], the canonical charts whose indices lie in [57,58) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b027 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
