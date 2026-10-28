-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1176
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1176
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:46:29.940756+00:00
-- url     : https://prove2.me/theorems/0f1533c7-cc0f-46e3-82ed-a6a40f2f130a
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 523/128 ≤ p ≤ 8369/2048
-- statement:
--   For every real p in [523/128,8369/2048], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1176 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
