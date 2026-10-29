-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p013_b025
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b025
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:51:17.839798+00:00
-- url     : https://prove2.me/theorems/7ccae797-4ba9-4489-94ec-b63e5a793e6a
-- title:
--   Hlawka distinct profile 13, finite certificate block 26
-- statement:
--   For p in [73/16,37/8], the canonical charts whose indices lie in [62,66) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b025 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
