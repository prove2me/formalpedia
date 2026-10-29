-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1432
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1432
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:35:42.7215+00:00
-- url     : https://prove2.me/theorems/16949260-9904-4641-97ae-1623241f2680
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 4391/1024 ≤ p ≤ 549/128
-- statement:
--   For every real p in [4391/1024,549/128], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1432 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
