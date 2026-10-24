-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_matrixSolutionOfNonzeroDet
-- name    : OAI.PiExponent.DeterminantContradiction.matrixSolutionOfNonzeroDet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:00:22.336612+00:00
-- url     : https://prove2.me/theorems/c1a6bb82-c194-4db6-8b2b-d704446bf456
-- title:
--   A nonzero determinant solves every square linear system
-- statement:
--   Every square complex matrix with nonzero determinant maps some coefficient vector to any prescribed right-hand side. This supplies the coefficients for the selected monomial construction. It also covers the empty index type, where the unique vector satisfies the empty system.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.matrixSolutionOfNonzeroDet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Complex) (hA : A.det ≠ 0) (y : ι → Complex) :
    ∃ x : ι → Complex, ∀ i : ι, ∑ j : ι, A i j * x j = y i := by
  sorry
