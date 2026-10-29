-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1436
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1436
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:36:14.606437+00:00
-- url     : https://prove2.me/theorems/87e9c181-9dd7-4bc4-8528-ed7aa35b9760
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4395/1024 ≤ p ≤ 1099/256
-- statement:
--   For every real p in [4395/1024,1099/256], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1436 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
