-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p007_b039
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p007_b039
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:26:52.533962+00:00
-- url     : https://prove2.me/theorems/c301555e-7d65-4a59-883c-7407d8094a28
-- title:
--   Hlawka repeated profile 7, finite certificate block 40
-- statement:
--   For p in [39/8,5], the canonical charts whose indices lie in [117,120) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p007_b039 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 323) (hlo : 117 ≤ c.val) (hhi : c.val < 120)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
