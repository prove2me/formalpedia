-- Prove2me | Theorems.Thm_OAI_Erdos3_affineComparisonContraction_bounds
-- name    : OAI.Erdos3.affineComparisonContraction_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:34.690135+00:00
-- url     : https://prove2.me/theorems/7bb7c9fb-5915-4e53-864e-1a3577768b70
-- title:
--   The affine comparison contraction lies in (0, 1/2] and is small against its moment factors
-- statement:
--   Let $\xi$ and $P$ be real numbers with $0 < \xi$ and $0 \le P$, and write $\lambda = $ `affineComparisonContraction ξ P`, OpenAI's real number defined as the reciprocal of `affineComparisonPrimeThreshold ξ P`. Then $0 < \lambda$, $\lambda \le 1/2$, and
--   $$\lambda \cdot \bigl(8 \cdot (1 + 2) \cdot (P + 2)\bigr)^2 \cdot \bigl(16\,(P + 2)\bigr)^2 \le \xi / 16.$$
--
--   Lean: `OAI.Erdos3.affineComparisonContraction_bounds` in `lean/OAI/Combinatorics/Progressions/Lattices/PrimeCoordinateCells.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/PrimeCoordinateCells.lean#L256

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem affineComparisonContraction_bounds {ξ P : ℝ} (hξ : 0 < ξ) (hP : 0 ≤ P) :
    0 < affineComparisonContraction ξ P ∧ affineComparisonContraction ξ P ≤ 1 / 2 ∧
    affineComparisonContraction ξ P * (8 * (1 + 2) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16 := by
  sorry

end Erdos3
end
end OAI
