-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p009
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p009
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:42:28.704993+00:00
-- url     : https://prove2.me/theorems/8e394be1-5fc2-460b-8d66-e848c345c66b
-- title:
--   Hlawka repeated coordinate localization for 41/8 ≤ p ≤ 21/4
-- statement:
--   For p in [41/8,21/4], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p009 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) :
    ∀ X orders signs, OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
