-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g002
-- name    : HlawkaSchatten.DiagonalCutoff4.real_cover_g002
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:51:33.569107+00:00
-- url     : https://prove2.me/theorems/3b6e1ed5-914f-4a91-bd77-3cde29c26693
-- title:
--   Sharp diagonal Hlawka real-three interval cover 3
-- statement:
--   The sharp cyclic constant satisfies the Hlawka inequality in real dimension three for every real p in [129/32,259/64].
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_cover_g002 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
