-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1031
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1031
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:38:58.295855+00:00
-- url     : https://prove2.me/theorems/bc8d207f-a16d-4877-9b65-224e3097ac38
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8223/2048 ≤ p ≤ 257/64
-- statement:
--   For every real p in [8223/2048,257/64], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1031 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
