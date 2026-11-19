-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingLaplaceDiagonalOffDiagonal
-- name    : Kyprianou.Ch01.branchingLaplaceDiagonalOffDiagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:53:03.499925+00:00
-- url     : https://prove2.me/theorems/7eb617de-9c7d-4a28-9dc5-35dfeabdd0e5
-- title:
--   branchingLaplaceDiagonalOffDiagonal
-- statement:
--   The exact source Laplace series decomposes into the diagonal population-one term and the discounted sum over all other states. The identity is an absolutely convergent PMF series for q>0; its proof uses the PMF real summability, exponential weights ≤1 and the tsum summand-splitting identity.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), source proof p.306; mass conservation and time-zero generator

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingLaplaceDiagonalOffDiagonal
    (law : PopulationLaws) (q : ℝ) (hq : 0 < q) (t : NNReal) :
    branchingLaplace law 1 t q =
      ((law 1 t) 1).toReal * Real.exp (-q) +
      (∑' k : ℕ, if k = 1 then (0 : ℝ)
        else ((law 1 t) k).toReal * Real.exp (-q * (k : ℝ))) := by
  sorry
