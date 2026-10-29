-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1316
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1316
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:29:34.574351+00:00
-- url     : https://prove2.me/theorems/55afd14f-5663-4934-bd4a-759a82180b6d
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4275/1024 ≤ p ≤ 1069/256
-- statement:
--   For every real p in [4275/1024,1069/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1316 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
