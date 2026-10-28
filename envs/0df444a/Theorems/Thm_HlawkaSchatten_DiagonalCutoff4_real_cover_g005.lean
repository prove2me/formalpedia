-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g005
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g005
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:53:55.597063+00:00
-- url     : https://prove2.me/theorems/d2c36b1a-2bb2-45c0-8a53-d9aa051d66b8
-- title:
--   Sharp diagonal Hlawka real-three interval cover 6
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [261/64,131/32].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g005 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
