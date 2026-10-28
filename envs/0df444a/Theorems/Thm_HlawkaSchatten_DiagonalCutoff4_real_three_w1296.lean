-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1296
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1296
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:54:49.534358+00:00
-- url     : https://prove2.me/theorems/97453358-113d-4b99-a9fb-f4d5e6e806f7
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4255/1024 ≤ p ≤ 133/32
-- statement:
--   For every real p in [4255/1024,133/32], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1296 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
