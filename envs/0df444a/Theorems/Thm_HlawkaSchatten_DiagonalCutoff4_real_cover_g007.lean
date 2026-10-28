-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g007
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:53:54.943613+00:00
-- url     : https://prove2.me/theorems/055549e3-795a-443d-aa8b-e0de93174172
-- title:
--   Sharp diagonal Hlawka real-three interval cover 8
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [263/64,33/8].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g007 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
