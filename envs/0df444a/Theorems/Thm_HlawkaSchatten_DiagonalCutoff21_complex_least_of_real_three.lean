-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three
-- name    : HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T13:01:49.502061+00:00
-- url     : https://prove2.me/theorems/6f78c968-f438-4a77-b0d4-e7e743d0acae
-- title:
--   A real three-coordinate bound gives the uniform least complex constant
-- statement:
--   For every real p>1, if the unchanged cyclic constant satisfies the original Hlawka inequality for all real three-coordinate triples, it is the least constant valid in every finite complex coordinate dimension, including dimension zero. Finite nonnegative mixtures of real circle projections preserve all seven norm powers up to a common positive circle moment; continuity passes the bound to the circle integral. The existing three-coordinate cyclic obstruction gives leastness. No equal-norm or nonzero-vector premise is used.
-- source:
--   Ezzeri Esa, Hlawka-Schatten construction (Apache-2.0), and @bwdaugherty, accepted cutoff32 submission 2d248eb1-4938-4dee-8392-df24d2c70f2f, https://prove2.me/theorems/6e8430ce-7c32-4b82-9a1b-d7fcd67fdeb3 . Generic transfer isolated and rebuilt for the cutoff21 proof by Yuxuan Xu. Original notices retained.

import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three :
    ∀ p : ℝ, 1 < p →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by sorry
