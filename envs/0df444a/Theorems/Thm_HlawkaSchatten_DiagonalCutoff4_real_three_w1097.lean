-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1097
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1097
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:58:16.10498+00:00
-- url     : https://prove2.me/theorems/f7b99cec-1723-4cdc-af96-d601e5c7b30f
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8289/2048 ≤ p ≤ 4145/1024
-- statement:
--   For every real p in [8289/2048,4145/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1097 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
