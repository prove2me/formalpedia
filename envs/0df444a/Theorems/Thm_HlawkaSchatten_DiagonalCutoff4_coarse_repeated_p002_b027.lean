-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p002_b027
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p002_b027
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:17:05.520773+00:00
-- url     : https://prove2.me/theorems/90861032-9980-4210-81d2-162c514a2abb
-- title:
--   Hlawka repeated profile 2, finite certificate block 28
-- statement:
--   For p in [17/4,35/8], the canonical charts whose indices lie in [81,84) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p002_b027 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 323) (hlo : 81 ≤ c.val) (hhi : c.val < 84)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
