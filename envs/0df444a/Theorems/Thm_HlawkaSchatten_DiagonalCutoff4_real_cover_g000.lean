-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g000
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g000
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:51:33.504152+00:00
-- url     : https://prove2.me/theorems/72b7aa6a-fd9a-4fb5-b24a-57a3aba01f2c
-- title:
--   Sharp diagonal Hlawka real-three interval cover 1
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [4,257/64].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g000 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
