-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingLaplaceExponential
-- name    : Kyprianou.Ch01.branchingLaplaceExponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:25:30.118619+00:00
-- url     : https://prove2.me/theorems/25a9aaee-6e6e-4fb8-87d2-0c83e412f553
-- title:
--   Exercise 1.11(i): exponential Laplace transform of continuous-time branching
-- statement:
--   For a branching population whose laws satisfy Definition 1.14, show E_y exp(-φY_t)=exp(-y u_t(φ)) for all integer y≥0, φ>0, where u_t is the negative logarithm of the one-ancestor Laplace transform. The independent-sum law, zero-ancestor absorption and transform positivity are the genuine model hypotheses; the desired exponential factorization is the conclusion. Draft uncompiled.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11, pp. 31–32.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingLaplaceExponential
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi) :
    ∀ (y : ℕ) (t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingLaplace law y t phi =
        Real.exp (-(y : ℝ) * branchingU law t phi) := by
  sorry
