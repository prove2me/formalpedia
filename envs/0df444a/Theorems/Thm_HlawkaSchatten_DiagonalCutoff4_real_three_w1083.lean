-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1083
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1083
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:51:05.836414+00:00
-- url     : https://prove2.me/theorems/38e976d6-e580-47cc-84e2-82d3be6415f3
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8275/2048 ≤ p ≤ 2069/512
-- statement:
--   For every real p in [8275/2048,2069/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1083 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
