-- Prove2me | Theorems.Thm_OAI_UniformSparsestCut_mainGap
-- name    : OAI.UniformSparsestCut.mainGap
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:36.382991+00:00
-- url     : https://prove2.me/theorems/bd259f1f-5d8d-4619-9b08-e63518f6976b
-- statement:
--   The theorem states that there exists a real constant c > 0 and, for each natural number j, a size n_j ≥ 2 together with a capacity C_j on n_j points (a nonnegative, symmetric function cap on pairs of indices in Fin n_j with zero diagonal), such that n_j tends to infinity as j → ∞, the value glValue(C_j) defined below is strictly positive for every j, and for all sufficiently large j the ratio OPT(C_j)/glValue(C_j) is at least c·√(log n_j)/(log log n_j)^3. Here OPT(C) is the infimum, over nonempty proper subsets B of the points, of the cut ratio: the total capacity across the cut between B and its complement divided by |B|(n − |B|). glValue(C) is the infimum of Σ_{i<j} cap(i,j)·d(i,j) over feasible d, where feasible means d is of negative type (d(i,j) = ‖x_i − x_j‖² for some vectors x_i in Euclidean space of dimension n, and d satisfies the triangle inequality d(i,k) ≤ d(i,j) + d(j,k)) and the sum of d(i,j) over pairs i<j equals 1. The statement is existential and is admitted without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/UniformSparsestCut.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/UniformSparsestCut.lean; bytes 1196..1579
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_UniformSparsestCut

namespace OAI

noncomputable section

open scoped BigOperators

namespace UniformSparsestCut

open Filter

theorem mainGap :
    ∃ c : ℝ, 0 < c ∧
      ∃ n : ℕ → ℕ, ∃ C : (j : ℕ) → Capacity (n j),
        (∀ j, 2 ≤ n j) ∧
        Tendsto n atTop atTop ∧
        (∀ j, 0 < glValue (C j)) ∧
        ∀ᶠ j in atTop,
          c * Real.sqrt (Real.log (n j : ℝ)) / (Real.log (Real.log (n j : ℝ))) ^ 3 ≤
            OPT (C j) / glValue (C j) := by
  sorry

end UniformSparsestCut
end
end OAI
