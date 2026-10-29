-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1376
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1376
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:11:30.21811+00:00
-- url     : https://prove2.me/theorems/264e3185-341c-4fa0-b2ba-9430a410b834
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4335/1024 ≤ p ≤ 271/64
-- statement:
--   For every real p in [4335/1024,271/64], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1376 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
