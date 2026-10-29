-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p006_b040
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p006_b040
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:11:57.369994+00:00
-- url     : https://prove2.me/theorems/eedb7eb3-cdba-4b11-ad5f-748523973c23
-- title:
--   Hlawka repeated profile 6, finite certificate block 41
-- statement:
--   For p in [19/4,39/8], the canonical charts whose indices lie in [120,123) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p006_b040 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 323) (hlo : 120 ≤ c.val) (hhi : c.val < 123)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
