-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1717
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1717
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:47:26.32599+00:00
-- url     : https://prove2.me/theorems/612806b1-f7af-4e22-bd66-bd7a842379bc
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 5351/1024 ≤ p ≤ 5359/1024
-- statement:
--   For every real p in [5351/1024,5359/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1717 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
