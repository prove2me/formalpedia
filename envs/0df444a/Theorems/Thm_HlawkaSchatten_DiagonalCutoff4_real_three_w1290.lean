-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1290
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1290
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:53:15.97383+00:00
-- url     : https://prove2.me/theorems/2778dedf-348c-46da-ac33-6a8a4d1e554d
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4249/1024 ≤ p ≤ 2125/512
-- statement:
--   For every real p in [4249/1024,2125/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1290 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
