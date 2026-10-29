-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1460
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1460
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:44:24.354995+00:00
-- url     : https://prove2.me/theorems/eb54459b-4c5b-4402-85c4-3b64737ccf9c
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4419/1024 ≤ p ≤ 1105/256
-- statement:
--   For every real p in [4419/1024,1105/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1460 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
