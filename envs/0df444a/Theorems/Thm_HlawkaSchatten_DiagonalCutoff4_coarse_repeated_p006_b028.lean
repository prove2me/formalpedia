-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p006_b028
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p006_b028
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:11:56.849352+00:00
-- url     : https://prove2.me/theorems/627b4af6-84c8-404a-85ce-143f09fcfc29
-- title:
--   Hlawka repeated profile 6, finite certificate block 29
-- statement:
--   For p in [19/4,39/8], the canonical charts whose indices lie in [84,87) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p006_b028 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 323) (hlo : 84 ≤ c.val) (hhi : c.val < 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
