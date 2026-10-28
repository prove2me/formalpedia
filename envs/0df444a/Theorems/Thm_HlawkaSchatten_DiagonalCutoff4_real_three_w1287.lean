-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1287
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1287
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:52:13.371439+00:00
-- url     : https://prove2.me/theorems/f646a146-901e-4de2-9a95-30df638a7b44
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 2123/512 ≤ p ≤ 4247/1024
-- statement:
--   For every real p in [2123/512,4247/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1287 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
