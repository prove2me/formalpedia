-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1050
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1050
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:54:12.565115+00:00
-- url     : https://prove2.me/theorems/205eabd5-9ccd-470f-acbf-b93d1e6e58c1
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4121/1024 ≤ p ≤ 8243/2048
-- statement:
--   For every real p in [4121/1024,8243/2048], the campaign cyclic constant satisfies the Hlawka inequality for all triples in real dimension three. There are no localization or sign hypotheses.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1050 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
