-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_coarse_failure_window26
-- name    : HlawkaSchatten.DiagonalCutoff21.coarse_failure_window26
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T10:57:19.61098+00:00
-- url     : https://prove2.me/theorems/22e714bd-0580-4d61-b6f5-2e74793d4a18
-- title:
--   Every real-three failure on [26,32] localizes to the coarse box
-- statement:
--   For every real $p\in[26,32]$, suppose arbitrary vectors $x,y,z\in\mathbb R^3$ strictly violate the Hlawka inequality with the unchanged cyclic constant $K_p$.
--
--   Then another strictly violating triple $X=(X_0,X_1,X_2)$ exists with singleton norms summing to $3$, total norm less than $3(197/500)$, pair-gap sum less than $2/((443/1000)p)$, diagonal entries in $[-1183/1000,-477/1000]$, and off-diagonal entries in $[3/4,1183/1000]$.
--
--   The input vectors are unrestricted: no equal-norm, nonzero, sign, coordinate, normalization or localization premise is imposed. Reflection, rescaling and simultaneous signed coordinate permutation are conclusions of the proof. This is a counterexample reduction, not an assertion that the final real-three Hlawka inequality is already proved.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Section 3, equations (10)-(11), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic normalization by Ezzeri Esa and cutoff-32 orientation by @bwdaugherty, Apache-2.0, adapted with the new constants.

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window26
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.coarse_failure_window26 :
    ∀ p : ℝ, 26 ≤ p → p ≤ 32 →
    ∀ x y z : Fin 3 → ℝ, hlawkaDeficit p (cyclicConstant p) x y z < 0 →
    ∃ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(1183/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(477/1000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3/4 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) ∧
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
      lpNorm p (X 0 + X 1 + X 2) < 3 * (197/500 : ℝ) ∧
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by sorry
