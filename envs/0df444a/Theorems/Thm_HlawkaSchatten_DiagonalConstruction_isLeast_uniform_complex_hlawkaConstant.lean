-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_isLeast_uniform_complex_hlawkaConstant
-- name    : HlawkaSchatten.DiagonalConstruction.isLeast_uniform_complex_hlawkaConstant
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T19:00:58.222144+00:00
-- url     : https://prove2.me/theorems/d828068e-8b2b-4f6d-86a9-7d6358026dfc
-- title:
--   The least uniform complex coordinate Hlawka constant for p ≥ 256
-- statement:
--   For a real exponent $p\ge256$ and $x\in\mathbb C^n$, let
--   $$
--   \|x\|_p=\left(\sum_{i=1}^n|x_i|^p\right)^{1/p}.
--   $$
--   For a triple $x,y,z$, put
--   $$
--   \Delta_3=\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p,
--   $$
--   $$
--   \Delta_2=2(\|x\|_p+\|y\|_p+\|z\|_p)
--   -\|x+y\|_p-\|x+z\|_p-\|y+z\|_p.
--   $$
--   Define the cyclic constant by the fixed compact interval
--   $$
--   K_p=\sup_{1/2\le t\le2}
--   \frac{3(t^p+2)^{1/p}-3^{1/p}|2-t|}
--   {6(t^p+2)^{1/p}-3(2|1-t|^p+2^p)^{1/p}}.
--   $$
--   The theorem states that $K_p$ is the least real constant $C$ such that
--   $\Delta_3\le C\Delta_2$ for every finite dimension $n$ and every triple in
--   $\mathbb C^n$. Thus it combines admissibility and dimension-independent
--   optimality in one `IsLeast` statement. Dimension zero is included and has
--   zero gaps. The lower-bound obstruction already occurs in dimension three;
--   the theorem does not assert that the same constant is best in dimensions
--   one or two. The coordinate norm agrees with the Schatten norm on diagonal
--   matrices, but the statement does not quantify over general matrices.
-- source:
--   Corollary of HlawkaSchatten.DiagonalConstruction.complex_hlawka_bound (https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ComplexTransfer.lean#L83) and HlawkaSchatten.DiagonalConstruction.cyclicConstant_le_of_complex_constant (https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/CyclicWitness.lean#L111).

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # The least dimension-independent complex coordinate Hlawka constant

This packages admissibility and the three-coordinate cyclic obstruction into
one statement, with an explicit lower cutoff on the real exponent.
-/

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.isLeast_uniform_complex_hlawkaConstant :
    ∀ p : ℝ, 256 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
