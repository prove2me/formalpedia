-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p010
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p010
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:48:55.854746+00:00
-- url     : https://prove2.me/theorems/0cd89ea1-e259-44ed-864f-1ace52abc430
-- title:
--   Hlawka repeated coordinate localization for 21/4 ≤ p ≤ 43/8
-- statement:
--   For p in [21/4,43/8], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p010 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
