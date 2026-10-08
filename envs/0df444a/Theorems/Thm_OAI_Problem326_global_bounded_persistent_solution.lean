-- Prove2me | Theorems.Thm_OAI_Problem326_global_bounded_persistent_solution
-- name    : OAI.Problem326.global_bounded_persistent_solution
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.709037+00:00
-- url     : https://prove2.me/theorems/8c2f866d-42e5-41e1-8403-b3673b9a6c98
-- statement:
--   The theorem states that, for every dimension d>0, every reaction network N on d species, and every assignment of strictly positive rate constants κ(e)>0 to the reactions of N, if N is weakly reversible then the following holds for every initial state x0 in ℝ^d with all coordinates strictly positive. Here a reaction network consists of finite sets of complexes (vectors in ℕ^d) and of reactions (ordered pairs of distinct complexes, source and target, both in the complex set); weak reversibility means that for each reaction y→z there is a chain of one or more reactions leading from z back to y. The mass-action vector field sends a state x to the vector whose ith coordinate is the sum over reactions y→z of κ(y→z) times the monomial ∏ⱼ xⱼ^{yⱼ} times (zᵢ−yᵢ). A global forward solution with initial value x0 is a function x:ℝ→ℝ^d with x(0)=x0 whose derivative at every time t≥0 equals this vector field evaluated at x(t). The conclusion is that there exists ε with 0<ε<1 such that a global forward solution exists, and every global forward solution satisfies ε ≤ xᵢ(t) ≤ 1/ε for all t≥0 and all coordinates i. In particular, solutions are bounded above and persistently bounded away from zero, with a uniform constant ε that works for all such solutions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MassAction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MassAction.lean; bytes 1432..1956
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MassAction

namespace OAI

noncomputable section

namespace Problem326

theorem global_bounded_persistent_solution :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
        ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ := by
  sorry

end Problem326
end
end OAI
