-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g009
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g009
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T14:53:58.996398+00:00
-- url     : https://prove2.me/theorems/bd032b19-bf46-43c7-9b3b-2f24d9e8a226
-- title:
--   Sharp diagonal Hlawka real-three interval cover 10
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [4247/1024,4279/1024].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g009 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
