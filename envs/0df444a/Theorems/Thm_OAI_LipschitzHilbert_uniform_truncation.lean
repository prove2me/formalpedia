-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_uniform_truncation
-- name    : OAI.LipschitzHilbert.uniform_truncation
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:53.673349+00:00
-- url     : https://prove2.me/theorems/1cb8e6f7-49a9-4b04-bc8f-76d33e33dcc2
-- statement:
--   The theorem states that there is a constant C>0 such that the following uniform L² bound holds for every K>0 (a nonnegative real Lipschitz constant), every pair of real numbers 0<ε≤R with R≤1/(10⁶K), every map v of the Euclidean plane ℝ² to itself that is K-Lipschitz and satisfies ‖v(x)‖=1 for all x, and every complex-valued Schwartz function f on ℝ². For the symmetrized truncated directional integral shortTransform(v,ε,R)f(x)=∫ from ε to R of t⁻¹(f(x−t·v(x))−f(x+t·v(x))) dt, the L²(ℝ²) norm with respect to Lebesgue measure (as an extended nonnegative real) is at most C times the L² norm of f. The constant C does not depend on K, v, ε, R or f, so the estimate is uniform at the truncation scale R bounded by the reciprocal of 10⁶ times the Lipschitz constant. The result is stated as admitted, without a proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LipschitzHilbert.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LipschitzHilbert.lean; bytes 3037..3507
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_LipschitzHilbert

namespace OAI

noncomputable section

attribute [-instance] instCommCStarAlgebraComplex

open MeasureTheory Set

open scoped ENNReal NNReal

namespace LipschitzHilbert

attribute [instance] instCommCStarAlgebraComplex

/-- The same uniform estimate at the reciprocal-Lipschitz truncation scale. -/
theorem uniform_truncation :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  sorry

end LipschitzHilbert
end
end OAI
