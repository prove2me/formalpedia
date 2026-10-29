-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1344
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1344
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:47:35.289175+00:00
-- url     : https://prove2.me/theorems/40f41eca-97c2-40ad-90a1-7fa41253e65c
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4303/1024 ≤ p ≤ 269/64
-- statement:
--   For every real p in [4303/1024,269/64], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1344 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
