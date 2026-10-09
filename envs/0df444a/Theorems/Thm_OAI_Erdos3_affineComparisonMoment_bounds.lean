-- Prove2me | Theorems.Thm_OAI_Erdos3_affineComparisonMoment_bounds
-- name    : OAI.Erdos3.affineComparisonMoment_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:30.697851+00:00
-- url     : https://prove2.me/theorems/fbf3dd33-29f1-48b6-95c1-b0713940e4ff
-- title:
--   The affine comparison moment is an even integer between P and P + 2
-- statement:
--   Let $P$ be a real number with $0 \le P$, and let $m = $ `affineComparisonMoment P` $= 2(\lfloor P/2 \rfloor + 1)$, a natural number (with the natural-number floor). Then $2 \le m$, $m$ is even, and $P \le m \le P + 2$ (as real numbers).
--
--   Lean: `OAI.Erdos3.affineComparisonMoment_bounds` in `lean/OAI/Combinatorics/Progressions/Lattices/AffinePrimitiveLogBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffinePrimitiveLogBudget.lean#L38

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem affineComparisonMoment_bounds {P : ℝ} (hP : 0 ≤ P) :
    2 ≤ affineComparisonMoment P ∧ Even (affineComparisonMoment P) ∧
    P ≤ (affineComparisonMoment P : ℝ) ∧ (affineComparisonMoment P : ℝ) ≤ P + 2 := by
  sorry

end Erdos3
end
end OAI
