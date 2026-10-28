-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g006
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g006
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:54:02.585531+00:00
-- url     : https://prove2.me/theorems/ce2d1d53-cb48-4e1f-b321-b85f2af15eeb
-- title:
--   Sharp diagonal Hlawka real-three interval cover 7
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [131/32,263/64].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g006 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
