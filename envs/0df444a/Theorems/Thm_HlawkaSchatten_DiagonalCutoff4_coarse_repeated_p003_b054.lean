-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b054
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b054
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:53:30.908406+00:00
-- url     : https://prove2.me/theorems/3ac175e1-4c78-47ab-a6a9-a41e189942d4
-- title:
--   Hlawka repeated profile 3, finite certificate block 55
-- statement:
--   For p in [35/8,9/2], the canonical charts whose indices lie in [162,165) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003_b054 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 323) (hlo : 162 ≤ c.val) (hhi : c.val < 165)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
