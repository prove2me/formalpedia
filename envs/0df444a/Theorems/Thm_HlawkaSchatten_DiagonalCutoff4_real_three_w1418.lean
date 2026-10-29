-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1418
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1418
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:33:19.339027+00:00
-- url     : https://prove2.me/theorems/d5494280-b7c4-4951-a4a5-2711985c60cb
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4377/1024 ≤ p ≤ 2189/512
-- statement:
--   For every real p in [4377/1024,2189/512], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1418 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
