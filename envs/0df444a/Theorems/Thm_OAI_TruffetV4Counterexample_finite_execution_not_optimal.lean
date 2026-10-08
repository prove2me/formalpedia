-- Prove2me | Theorems.Thm_OAI_TruffetV4Counterexample_finite_execution_not_optimal
-- name    : OAI.TruffetV4Counterexample.finite_execution_not_optimal
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:35.35829+00:00
-- url     : https://prove2.me/theorems/897a7f95-0f96-4a91-b101-b4b3c8711114
-- statement:
--   The theorem states a concrete finite counterexample in a max-plus style elimination procedure on states with two variables (indices 0 and 1) and a third coordinate 2 that is the target coordinate. Forms are triples of coefficients in ℝ ∪ {−∞}, evaluated at w ∈ ℝ³ as the maximum of f(k)+w(k); a row is feasible when its right form evaluates at most its left form, and a state is stopped when every row's right coefficient at coordinate 2 is at most its left one. The initial state has row 0 with left (0,0,−∞) and right (−∞,−∞,0), row 1 with left (0,−∞,−∞) and right (−∞,1,−2), cost form (0,−∞,−∞), and both variables remaining. The middle state has row 0 empty (all −∞), row 1 with left (0,−∞,−∞) and right (−∞,−∞,1), the same cost, and only variable 0 remaining. The final state has all rows empty, cost (−∞,−∞,1), and no variable remaining. The statement asserts all of the following together: the initial state satisfies the cross-row restriction (for any two distinct rows i and r and any real α, some w makes the left form of row i evaluate strictly below α plus the right form of row r); passing from initial to middle is a forced singleton step using row 0 and variable 1, and passing from middle to final is a forced singleton step using row 1 and variable 0 (each step requiring well-formedness, boundedness, non-stopped, non-switch, non-failure, row-variable uniqueness among eligible pairs, and a non-trivial substituted cost, with the next state obtained by substitution and cleanup); no variable remains in the final state and the final state is stopped. Further, the points output = (1,0,0) and better = (0,−1,0) are both feasible for the initial state and both have third coordinate 0; output satisfies output(1) equal to the evaluation of the lower form of initial row 0 for variable 1, and output(0) equal to the evaluation of the lower form of middle row 1 for variable 0; the initial cost evaluated at output equals the final cost evaluated at output; but the initial cost evaluated at better is strictly less than the final cost evaluated at output, so the finite execution's output is not optimal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TruffetCounterexample.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TruffetCounterexample.lean; bytes 3907..4504
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TruffetCounterexample

namespace OAI

noncomputable section

namespace TruffetV4Counterexample

theorem finite_execution_not_optimal :
    crossRowRestriction initial ∧
    ForcedSingletonStep initial middle 0 1 ∧
    ForcedSingletonStep middle finalState 1 0 ∧
    (¬ ∃ j, finalState.remaining j) ∧ stop finalState ∧
    feasible initial output ∧ feasible initial better ∧
    output 2 = 0 ∧ better 2 = 0 ∧
    (output 1 : Coeff) = eval (lowerForm initial 0 1) output ∧
    (output 0 : Coeff) = eval (lowerForm middle 1 0) output ∧
    eval initial.cost output = eval finalState.cost output ∧
    eval initial.cost better < eval finalState.cost output := by
  sorry

end TruffetV4Counterexample
end
end OAI
