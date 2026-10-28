-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1175
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1175
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:46:17.423986+00:00
-- url     : https://prove2.me/theorems/0ea3f657-272c-4960-b104-982e74fefc96
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8367/2048 ≤ p ≤ 523/128
-- statement:
--   For every real p in [8367/2048,523/128], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1175 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
