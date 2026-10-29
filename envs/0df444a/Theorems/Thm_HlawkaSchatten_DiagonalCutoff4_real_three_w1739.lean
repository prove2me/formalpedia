-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1739
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1739
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:55:53.149289+00:00
-- url     : https://prove2.me/theorems/3b45a297-981c-4314-bb92-640641f6c95e
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 5583/1024 ≤ p ≤ 5599/1024
-- statement:
--   For every real p in [5583/1024,5599/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1739 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
