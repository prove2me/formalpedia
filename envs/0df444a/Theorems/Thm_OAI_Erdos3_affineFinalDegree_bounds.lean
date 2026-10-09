-- Prove2me | Theorems.Thm_OAI_Erdos3_affineFinalDegree_bounds
-- name    : OAI.Erdos3.affineFinalDegree_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:49:11.200134+00:00
-- url     : https://prove2.me/theorems/6510401b-f7e6-4774-b362-585265cf9bf8
-- title:
--   The affine final degree dominates j + r and j + the spectral iteration count
-- statement:
--   For all natural numbers $j,r$ and real numbers $\mathit{shell},Q$, both $j+r\le$ `affineFinalDegree j r shell Q` and $j+$ `CyclicCrootSisask.spectralIterations shell Q` $\le$ `affineFinalDegree j r shell Q`. Here `affineFinalDegree j r shell Q` is the natural number $j+\max(r,\ \texttt{spectralIterations}\ \mathit{shell}\ Q)$, and `CyclicCrootSisask.spectralIterations ε p` is the natural number $\lceil (p+\log(16/\varepsilon))/\log 2\rceil_+ +1$ (natural logarithm, $\lceil\cdot\rceil_+$ the ceiling into $\mathbb N$).
--
--   Lean: `OAI.Erdos3.affineFinalDegree_bounds` in `lean/OAI/Combinatorics/Progressions/Polynomial/AffineDegreeChoice.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/AffineDegreeChoice.lean#L36

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem affineFinalDegree_bounds (j r : ℕ) (shell Q : ℝ) :
    j + r ≤ affineFinalDegree j r shell Q ∧
    j + CyclicCrootSisask.spectralIterations shell Q ≤ affineFinalDegree j r shell Q := by
  sorry

end Erdos3
end
end OAI
