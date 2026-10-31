-- Prove2me | Theorems.Thm_KnapsackFacets_lemma_2
-- name    : KnapsackFacets.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:30.95833+00:00
-- url     : https://prove2.me/theorems/2bbb6783-af93-4b5a-bc89-c4841f60896e
-- title:
--   Lemma 2 ([6]) — $\frac{\sqrt2-1}{4}\sqrt2^{\,j}\le f_j\le 2^j$ for $j\ge3$
-- statement:
--   **Lemma 2.** For the shifted Fibonacci sequence $f$ of (1)–(2) and every $j\ge3$,
--   $$
--   \frac{\sqrt2-1}{4}\,\sqrt2^{\,j}\ \le\ f_j\ \le\ 2^j .
--   $$
--
--   The lower bound gives Claim A, which fixes how large $r$ must be in the reduction of Theorem 4.
--
--   Differences from the source: none.
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Lemma 2, p.6

import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

namespace KnapsackFacets

/-- **Lemma 2 ([6]).** "For j ≥ 3, (√2−1)/4 · √2ʲ ≤ f_j ≤ 2ʲ." Chen & Zhu,
arXiv:2211.03311v3, Lemma 2, p.6 (read on the rendered page; the text layer garbles the
fraction).

**Formalization Note.** The inequalities are in `ℝ`, with `f = shiftedFib`. -/
theorem lemma_2 (j : ℕ) (hj : 3 ≤ j) :
    (Real.sqrt 2 - 1) / 4 * Real.sqrt 2 ^ j ≤ (shiftedFib j : ℝ) ∧
      (shiftedFib j : ℝ) ≤ 2 ^ j := by sorry

end KnapsackFacets
