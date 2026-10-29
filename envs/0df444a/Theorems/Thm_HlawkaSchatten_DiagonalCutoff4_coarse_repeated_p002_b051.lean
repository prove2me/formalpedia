-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p002_b051
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p002_b051
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:18:04.56365+00:00
-- url     : https://prove2.me/theorems/9d10574c-e0f1-4b1b-b8f8-ae00051daa9b
-- title:
--   Hlawka repeated profile 2, finite certificate block 52
-- statement:
--   For p in [17/4,35/8], the canonical charts whose indices lie in [153,156) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p002_b051 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 323) (hlo : 153 ≤ c.val) (hhi : c.val < 156)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
