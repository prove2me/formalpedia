-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalPairCoefficientLog_bounds
-- name    : OAI.Erdos3.physicalPairCoefficientLog_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:25:34.450963+00:00
-- url     : https://prove2.me/theorems/c2559fb7-6605-46df-aab6-8947dad32857
-- title:
--   The physical pair coefficient logarithm dominates its constituent budgets
-- statement:
--   Let $n$ and $d$ be natural numbers and $P$ a real number with $0 \le P$, and write $\Lambda = $ `physicalPairCoefficientLog n d P` $= 30 + 2nP + 2n + \sigma + n(5P + 11) + 10P + 4(2 + d)$, where $\sigma = $ `smoothPairErrorLog n d P` is an explicit real-valued function of OpenAI. Then $0 \le \Lambda$, $P \le \Lambda$, $6 + 2nP + 2n + \sigma \le \Lambda$, $2 + 4(2 + d) + P \le \Lambda$, and $20 + 2nP + 2n + n(5P + 11) + 9P \le \Lambda$.
--
--   Lean: `OAI.Erdos3.physicalPairCoefficientLog_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/PhysicalPairAccuracyLogBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PhysicalPairAccuracyLogBounds.lean#L477

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physicalPairCoefficientLog_bounds (n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalPairCoefficientLog n d P ∧
    P ≤ physicalPairCoefficientLog n d P ∧
    6 + 2 * n * P + 2 * n + smoothPairErrorLog n d P ≤ physicalPairCoefficientLog n d P ∧
    2 + 4 * (2 + d) + P ≤ physicalPairCoefficientLog n d P ∧
    20 + 2 * n * P + 2 * n + n * (5 * P + 11) + 9 * P ≤ physicalPairCoefficientLog n d P := by
  sorry

end Erdos3
end
end OAI
