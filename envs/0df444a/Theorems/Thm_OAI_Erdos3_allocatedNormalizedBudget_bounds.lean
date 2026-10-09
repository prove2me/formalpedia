-- Prove2me | Theorems.Thm_OAI_Erdos3_allocatedNormalizedBudget_bounds
-- name    : OAI.Erdos3.allocatedNormalizedBudget_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:43:12.522228+00:00
-- url     : https://prove2.me/theorems/b488b566-bcec-4ed9-867b-b213f603a397
-- title:
--   The allocated normalized budget dominates the child cost and the number of variables
-- statement:
--   Let $s$ and $\mathrm{cardVars}$ be natural numbers and $\mathrm{childCost}$ a real number with $0 \le \mathrm{childCost}$. Let $E$ be the natural number chosen (by `Classical.choose`, at universe levels $0, 0$) as the witness of OpenAI's theorem `exists_relative_finite_returned_fiber_normalization s`, which asserts the existence of a natural number $E \ge 2$ with a certain fiber-normalization property; and let $B = \bigl((\mathrm{childCost} + \mathrm{cardVars} + 2) + 2\bigr)^E$. Then $\mathrm{childCost} \le B$, $0 \le B$, and $\mathrm{cardVars} \le B$.
--
--   Lean: `OAI.Erdos3.allocatedNormalizedBudget_bounds` in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedNormalizationPrimitiveBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B032` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedNormalizationPrimitiveBudget.lean#L13

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B032

namespace OAI

section

namespace Erdos3

theorem allocatedNormalizedBudget_bounds (s cardVars : ℕ) {childCost : ℝ}
    (hchild : 0 ≤ childCost) :
    let E := (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose
    let B := ((childCost + (cardVars : ℝ) + 2) + 2) ^ E
    childCost ≤ B ∧ 0 ≤ B ∧ (cardVars : ℝ) ≤ B := by
  sorry

end Erdos3
end
end OAI
