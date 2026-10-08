-- Prove2me | Theorems.Thm_OAI_Erdos3_affineComparisonAccuracy_gram
-- name    : OAI.Erdos3.affineComparisonAccuracy_gram
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:00:35.540328+00:00
-- url     : https://prove2.me/theorems/c03ce167-3e14-4987-a90d-15fb513ce6c8
-- title:
--   affineComparisonAccuracy absorbs the low-degree coordinate-set count
-- statement:
--   Let $\iota$ be a finite type with decidable equality, $P,L,T$ real numbers and $b$ a natural number, with $0\le P$, $0\le L$, $0\le T$ and $|\iota|\le e^P$. Write $a$ for `affineComparisonAccuracy b P L T`, the real number $\exp\big(-((P+3)^3+2b(P+2)+L+T+4)\big)$, and $m$ for the cardinality of `lowDegreeCoordinateSets ι b`, the finite set of subsets $S\subseteq\iota$ with $|S|\le b$. Then
--   $$2\,a\,m^2\,4^b\,(1+a)^2\le e^{-T}.$$
--
--   Lean: `OAI.Erdos3.affineComparisonAccuracy_gram` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineResidueAccuracy.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B010` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineResidueAccuracy.lean#L37

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B010

namespace OAI

section

namespace Erdos3

theorem affineComparisonAccuracy_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P L T : ℝ} (b : ℕ) (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    2 * affineComparisonAccuracy b P L T * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + affineComparisonAccuracy b P L T) ^ 2 ≤ Real.exp (-T) := by
  sorry

end Erdos3
end
end OAI
