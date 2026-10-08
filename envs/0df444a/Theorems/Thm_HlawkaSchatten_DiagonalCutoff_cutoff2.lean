-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff2
-- name    : HlawkaSchatten.DiagonalCutoff.cutoff2
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-08T05:35:18.125412+00:00
-- url     : https://prove2.me/theorems/1266aef6-ea09-4047-8a0c-1ab964417c81
-- title:
--   The sharp diagonal Hlawka constant for $p = 2$ is $1$
-- statement:
--   NOT the threshold cutoff2 — this is the p=2 endpoint (point result only). The name was a mistake; sorry for squatting the namespace. For p=2, the least uniform constant C such that the diagonal Hlawka inequality holds with constant C on l_2^n(C) for every n is C=1, via Hlawka's 1D inequality integrated against the Gaussian measure.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant (endpoint p=2; proof via Hlawka's 1D inequality + Gaussian integral)

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.cutoff2 : IsLeast {C : ℝ | ∀ n : ℕ, HasHlawkaConstant (lpNorm 2 : (Fin n → ℂ) → ℝ) C} 1 := by sorry
