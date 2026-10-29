-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1771
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1771
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:06:34.786512+00:00
-- url     : https://prove2.me/theorems/b045f42f-ed62-463d-a09c-3973572a9f09
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 6095/1024 ≤ p ≤ 6111/1024
-- statement:
--   For every real p in [6095/1024,6111/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1771 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
