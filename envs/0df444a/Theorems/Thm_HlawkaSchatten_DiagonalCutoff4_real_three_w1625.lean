-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1625
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1625
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:09:16.466267+00:00
-- url     : https://prove2.me/theorems/2663c4da-94b9-4097-b5ad-b056a082b35f
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4815/1024 ≤ p ≤ 4819/1024
-- statement:
--   For every real p in [4815/1024,4819/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1625 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
