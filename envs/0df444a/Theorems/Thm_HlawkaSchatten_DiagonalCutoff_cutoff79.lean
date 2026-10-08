-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff79
-- name    : HlawkaSchatten.DiagonalCutoff.cutoff79
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-07T10:39:30.424352+00:00
-- url     : https://prove2.me/theorems/fe7d71c4-9865-4f52-a06b-0abf858c7a7a
-- title:
--   Sharp diagonal Hlawka constant for p ≥ 79 (complex case)
-- statement:
--   For every real $p \ge 79$, the cyclic constant is the least Hlawka constant for complex diagonal matrices.

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

theorem HlawkaSchatten.DiagonalCutoff.cutoff79 : ∀ p : ℝ, 79 ≤ p → IsLeast {C : ℝ | ∀ n : ℕ, HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by sorry
