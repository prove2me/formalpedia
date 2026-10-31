-- Prove2me | Theorems.Thm_KnapsackFacets_lemma_3
-- name    : KnapsackFacets.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:27.781202+00:00
-- url     : https://prove2.me/theorems/31b30900-a115-4acf-86e2-123a270b5973
-- title:
--   Lemma 3 ([6]) — every $\tau\le\sum_{i=1}^{2r+1}f_i$ is a subset sum of $f_1,\dots,f_{2r+1}$
-- statement:
--   **Lemma 3.** Let $f$ be the shifted Fibonacci sequence of (1)–(2) and $r\ge1$ an integer. For every integer $\tau$ with $0\le\tau\le\sum_{i=1}^{2r+1}f_i$ there is a subset $S\subseteq[2r+1]$ with
--   $$
--   f(S)=\sum_{i\in S}f_i=\tau .
--   $$
--
--   It supplies the tight points in Claims C and D of the proof of Theorem 4.
--
--   Differences from the source:
--   - encoding: τ ∈ ℤ₊ with 0 ≤ τ → τ : ℕ; reason: nonnegative integers are the natural numbers
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Lemma 3, p.6

import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

namespace KnapsackFacets

/-- **Lemma 3 ([6]).** "Let f be defined as in (1)-(2) and r ≥ 1 be a given integer. For any
τ ∈ ℤ₊ satisfying 0 ≤ τ ≤ Σ_{i=1}^{2r+1} fᵢ, there exists a subset S ⊆ [2r + 1] such that
f(S) = τ." Chen & Zhu, arXiv:2211.03311v3, Lemma 3, p.6.

**Formalization Note.** `τ : ℕ` (so `0 ≤ τ` is automatic), `[2r + 1] = Finset.Icc 1 (2r+1)`
and `f(S) = Σ_{i ∈ S} fᵢ`. -/
theorem lemma_3 (r : ℕ) (hr : 1 ≤ r) (τ : ℕ)
    (hτ : τ ≤ ∑ i ∈ Finset.Icc 1 (2 * r + 1), shiftedFib i) :
    ∃ S ⊆ Finset.Icc 1 (2 * r + 1), ∑ i ∈ S, shiftedFib i = τ := by sorry

end KnapsackFacets
