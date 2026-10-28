-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g001
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g001
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:51:32.287747+00:00
-- url     : https://prove2.me/theorems/1b17a788-70bc-4f0a-893b-2b6d006e4453
-- title:
--   Sharp diagonal Hlawka real-three interval cover 2
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [257/64,129/32].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g001 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
