-- Prove2me | Theorems.Thm_OAI_Erdos3_replacementCommonInputLog_bounds
-- name    : OAI.Erdos3.replacementCommonInputLog_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T18:02:08.583463+00:00
-- url     : https://prove2.me/theorems/9e8ee6c2-1d00-4aa3-a25e-d51be8d1dcee
-- title:
--   The common replacement input logarithm dominates P and the cutoff input logarithm
-- statement:
--   Let $m, n, d$ be natural numbers and $P$ a real number with $0 \le P$. Write $\gamma = $ `replacementCutoffInputLog m n d P` (an explicit real-valued function of OpenAI) and $Z = $ `replacementCommonInputLog m n d P` $= 4\gamma + 2P + 10$. Then $0 \le Z$, $P \le Z$, $\gamma \le Z$, $4\gamma + 6 \le Z$, $3\gamma + 6 \le Z$, and $2P + 3 \le Z$.
--
--   Lean: `OAI.Erdos3.replacementCommonInputLog_bounds` in `lean/OAI/Combinatorics/Progressions/Dynamics/InitialBudgetJointReplacement.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/InitialBudgetJointReplacement.lean#L33

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem replacementCommonInputLog_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ replacementCommonInputLog m n d P ∧
    P ≤ replacementCommonInputLog m n d P ∧
    replacementCutoffInputLog m n d P ≤ replacementCommonInputLog m n d P ∧
    4 * replacementCutoffInputLog m n d P + 6 ≤ replacementCommonInputLog m n d P ∧
    3 * replacementCutoffInputLog m n d P + 6 ≤ replacementCommonInputLog m n d P ∧
    2 * P + 3 ≤ replacementCommonInputLog m n d P := by
  sorry

end Erdos3
end
end OAI
