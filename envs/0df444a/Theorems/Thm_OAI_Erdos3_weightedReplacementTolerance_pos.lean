-- Prove2me | Theorems.Thm_OAI_Erdos3_weightedReplacementTolerance_pos
-- name    : OAI.Erdos3.weightedReplacementTolerance_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:37:16.781829+00:00
-- url     : https://prove2.me/theorems/1a24633b-5ed2-4ba9-b288-2b1605352ac8
-- title:
--   The weighted replacement tolerance is positive
-- statement:
--   Let $F, E, \varepsilon$ be real numbers with $0 \le E$ and $0 < \varepsilon$. Then $0 < $ `weightedReplacementTolerance F E ε`, where OpenAI defines `weightedReplacementTolerance F E ε` $= $ `replacementAccuracy` $(F^2(1+E), \varepsilon^2)$ and `replacementAccuracy B δ` $= \min\bigl(1, \delta/(1+B)\bigr)$; that is, $0 < \min\bigl(1, \varepsilon^2/(1 + F^2(1+E))\bigr)$.
--
--   Lean: `OAI.Erdos3.weightedReplacementTolerance_pos` in `lean/OAI/Combinatorics/Progressions/Estimates/SmallWeightedPhysicalReplacement.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/SmallWeightedPhysicalReplacement.lean#L14

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem weightedReplacementTolerance_pos {F E epsilon : ℝ}
    (hE : 0 ≤ E) (heps : 0 < epsilon) :
    0 < weightedReplacementTolerance F E epsilon := by
  sorry

end Erdos3
end
end OAI
