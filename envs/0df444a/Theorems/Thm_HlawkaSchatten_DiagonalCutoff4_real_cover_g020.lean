-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g020
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g020
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:54:03.69846+00:00
-- url     : https://prove2.me/theorems/9cde5e5e-2f69-4692-8f7e-7ae8188cb5ad
-- title:
--   Sharp diagonal Hlawka real-three interval cover 21
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [4875/1024,5003/1024].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g020 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
