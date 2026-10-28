-- Prove2me | Theorems.Thm_MarkovProcess_dyadic_bound_normalization
-- name    : MarkovProcess.dyadic_bound_normalization
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:10:23.536219+00:00
-- url     : https://prove2.me/theorems/9fb27401-fc1e-46d8-a397-ce322275399a
-- title:
--   Normalize Kolmogorov dyadic grid increment union bound
-- statement:
--   At level $n$, multiplying the number of dyadic cells by the Kolmogorov increment probability quotient at the threshold $2^{-n\gamma}$ is exactly $M$ times the $n$th power of the geometric decay ratio $2^{1-q+p\gamma}$. The proof handles extended nonnegative real finiteness and uses the original algebraic rearrangement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L82-L121

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_DyadicIncrementScalars
open MarkovProcess MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem MarkovProcess.dyadic_bound_normalization (p q γ : ℝ) (M : ℝ≥0) (n : ℕ) :
    (2 : ℝ≥0∞) ^ n *
        ((M : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q /
          dyadicIncrementThreshold γ n ^ p) =
      ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) := by sorry
