-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p001_b103
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b103
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:25:40.531582+00:00
-- url     : https://prove2.me/theorems/b14d4e6f-6d03-4cb6-a212-468490d0e127
-- title:
--   Hlawka repeated profile 1, finite certificate block 104
-- statement:
--   For p in [33/8,17/4], the canonical charts whose indices lie in [269,271) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b103 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 269 ≤ c.val) (hhi : c.val < 271)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
