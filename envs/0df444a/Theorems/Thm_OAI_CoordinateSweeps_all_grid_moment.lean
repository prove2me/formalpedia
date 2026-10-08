-- Prove2me | Theorems.Thm_OAI_CoordinateSweeps_all_grid_moment
-- name    : OAI.CoordinateSweeps.all_grid_moment
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:29.147621+00:00
-- url     : https://prove2.me/theorems/1dee102d-9af6-47b1-afe1-67ae4d7b5133
-- statement:
--   The theorem states that, for the coordinate-sweep model on rectangular grids with power-of-two side lengths, a quantitative moment bound holds uniformly over all allowed grids under explicit scale and perturbation hypotheses. Let q = 65536000000 and e0 = 1/10000. Assume r is a natural number with r ≥ 1, (2/e0)² ≤ r·log 2 and 4/e0 ≤ r·log 2; assume the sparse-scalar scale-readiness condition for r (r ≥ 2, r·log 2 ≥ 1, a numerical absorption inequality, and that every real s ≥ 2^r satisfies a list of explicit size inequalities); and assume that for every grid G whose side-length exponents all lie in [r, 2r], the total size s = G.size (the product of the side lengths 2^{bits j}) satisfies the main-size readiness inequalities for q (log s ≥ 1 and three explicit power-of-s inequalities). Let zStar satisfy the sparse-perturbation condition: 0 < zStar ≤ 1/(4·((2^{2r})!)²), and for every grid with at most 12800 coordinates and allowed exponents, every z in [0, zStar], and every nonempty set E of line-permutation choices, the sum of absolute differences between the choice probabilities at z and at 0, each conditioned on E, is less than an explicit slack depending on s. Then for every z in [0, zStar] and every allowed grid G, the MomentBound holds: for every number h of disjoint hole paths, every feasible hole configuration H, and every unitary irreducible representation σ of the stabilizer of H (the permutations fixing the starting hole positions), the unnormalized Schatten 2q moment Re tr((K*K)^q) of the conditional average K of σ over residuals of compatible choices, weighted by the (1−z)U + zB line law, is at most exp(−c(s)·log dim σ + e(s)·h·log s − cost(H)), where c(s) = 1/10000 + 1/√(log s), e(s) = e0 − 1/√(log s), and cost(H) is the sum over coordinates and lines of log of (2^{bits j})^m divided by the falling factorial of 2^{bits j} of length m, with m the number of hole paths on that line.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoordinateSweeps.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoordinateSweeps.lean; bytes 10918..11356
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CoordinateSweeps

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ComplexConjugate MatrixOrder ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

/-- The quantitative all-grid estimate under the explicit scale and perturbation bounds. -/
theorem all_grid_moment {r : ℕ} (hr : ScaleLarge r) (hrS : SparseScalar.ScaleReady r)
    (hS : ∀ G : Grid, G.Allowed r → ScalarInduction.MainSizeReady SparseScalar.q G.size)
    {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z∈Set.Icc 0 zStar) :
    ∀ G : Grid, G.Allowed r → MomentBound G SparseScalar.q z := by
  sorry

end CoordinateSweeps
end
end OAI
