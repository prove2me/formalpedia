-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1163
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1163
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:40:49.154793+00:00
-- url     : https://prove2.me/theorems/467f37a5-85f0-4df5-b10e-edff2b48967e
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 8355/2048 ≤ p ≤ 2089/512
-- statement:
--   For every real p in [8355/2048,2089/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1163 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
