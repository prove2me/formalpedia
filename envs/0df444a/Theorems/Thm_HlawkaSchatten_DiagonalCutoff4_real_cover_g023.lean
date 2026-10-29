-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g023
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g023
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:54:02.322249+00:00
-- url     : https://prove2.me/theorems/eef6e096-5e62-481d-9e4b-31f0ae535219
-- title:
--   Sharp diagonal Hlawka real-three interval cover 24
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [5535/1024,6047/1024].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g023 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
