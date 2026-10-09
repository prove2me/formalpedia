-- Prove2me | Theorems.Thm_OAI_Erdos3_affineComparisonScale_bounds
-- name    : OAI.Erdos3.affineComparisonScale_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:56.090203+00:00
-- url     : https://prove2.me/theorems/454616de-f38b-44d5-89d4-c4b0fa65ee6f
-- title:
--   The affine comparison scale dominates each of its summands
-- statement:
--   Let $\varepsilon, L, T, C$ be real numbers with $0 \le L$, $0 \le T$ and $0 \le C$ ($\varepsilon$ is arbitrary). Let $s = $ `affineComparisonScale ε L T C` $= L + T + 2 + (\texttt{affineRemovalDepth}\ T + \texttt{affineComparisonTail}\ \varepsilon\ L\ T) + C$, where `affineRemovalDepth T` and `affineComparisonTail ε L T` are natural numbers defined by OpenAI (their sum is cast to $\mathbb{R}$). Then $0 \le s$, $L + T + 2 \le s$, $\texttt{affineRemovalDepth}\ T + \texttt{affineComparisonTail}\ \varepsilon\ L\ T \le s$, and $C \le s$.
--
--   Lean: `OAI.Erdos3.affineComparisonScale_bounds` in `lean/OAI/Combinatorics/Progressions/Lattices/AffinePrimitiveLogBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffinePrimitiveLogBudget.lean#L18

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem affineComparisonScale_bounds {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    0 ≤ affineComparisonScale ε L T C ∧
    L + T + 2 ≤ affineComparisonScale ε L T C ∧
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤ affineComparisonScale ε L T C ∧
    C ≤ affineComparisonScale ε L T C := by
  sorry

end Erdos3
end
end OAI
