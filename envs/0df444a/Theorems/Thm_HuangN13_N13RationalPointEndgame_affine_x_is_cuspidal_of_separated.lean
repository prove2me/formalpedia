-- Prove2me | Theorems.Thm_HuangN13_N13RationalPointEndgame_affine_x_is_cuspidal_of_separated
-- name    : HuangN13.N13RationalPointEndgame.affine_x_is_cuspidal_of_separated
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:45:35.606903+00:00
-- url     : https://prove2.me/theorems/2e9a8382-85ba-45fd-90b5-75cfd32952f1
-- title:
--   Separated compatible reduction gives cuspidal rational points
-- statement:
--   For a compatible reduction with separated kernel, the original injectivity and cusp-classification arguments identify each rational curve point with a cusp. Apply the first-coordinate map to this equality. The two infinite cusps cannot equal an affine point, and the remaining cusp cases give first coordinate zero or minus one.
-- source:
--   Xiang Huang, Apache-2.0. Original source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13RationalPointEndgame.lean; exact unit8 lines400-436, source-command SHA-256 413088bf478acf03769158ec43558c3c8fd6c1fab340452749a797242ce9da01. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4

set_option autoImplicit false

theorem HuangN13.N13RationalPointEndgame.affine_x_is_cuspidal_of_separated (D : MazurProof.N13RationalPointEndgame.CompatibleReduction) (separated : MazurProof.N18RouteC.Separated.NSeparated D.classifier.red.ker 2) : ∀ X Y : ℚ, MazurProof.N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1 := by sorry
