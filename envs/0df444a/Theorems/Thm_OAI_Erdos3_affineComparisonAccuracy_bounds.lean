-- Prove2me | Theorems.Thm_OAI_Erdos3_affineComparisonAccuracy_bounds
-- name    : OAI.Erdos3.affineComparisonAccuracy_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:30:15.323089+00:00
-- url     : https://prove2.me/theorems/2a98592f-c3b6-4e51-9047-90ff6f1322b6
-- title:
--   Bounds on affineComparisonAccuracy b P L T
-- statement:
--   Let $P,L,T,\mathrm{level}$ be real numbers and $b$ a natural number, with $0\le P$, $0\le L$, $0\le T$ and $e^{-L}\le\mathrm{level}$. Write $a$ for `affineComparisonAccuracy b P L T`, the real number $\exp\big(-((P+3)^3+2b(P+2)+L+T+4)\big)$. Then $0<a$, $a<1$, $a\le e^{-T}/8$, $a\le \mathrm{level}\cdot e^{-T}/8$, and $a\le \tfrac12\exp\big(-(P+3)^3\big)$.
--
--   Lean: `OAI.Erdos3.affineComparisonAccuracy_bounds` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineResidueAccuracy.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B009` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineResidueAccuracy.lean#L15

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

namespace OAI

section

namespace Erdos3

theorem affineComparisonAccuracy_bounds {P L T level : ℝ} (b : ℕ)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T) (hlevel : Real.exp (-L) ≤ level) :
    0 < affineComparisonAccuracy b P L T ∧ affineComparisonAccuracy b P L T < 1 ∧
    affineComparisonAccuracy b P L T ≤ Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ level * Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)) := by
  sorry

end Erdos3
end
end OAI
