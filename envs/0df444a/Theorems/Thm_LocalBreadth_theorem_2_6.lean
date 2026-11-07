-- Prove2me | Theorems.Thm_LocalBreadth_theorem_2_6
-- name    : LocalBreadth.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:27.013086+00:00
-- url     : https://prove2.me/theorems/ca5750b4-d6e2-4658-adc0-5e53e7b64c75
-- title:
--   Theorem 2.6 — the combinatorial and topological values coincide
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   For every $K\in\mathcal X$ and every positive integer $n$,
--   $$b_n(K)=\sup_{\substack{U\subseteq\mathcal H_K\text{ open}\\(K)\in U}}\ \inf_{H\in U}c_n(H).$$
--
--   The paper restates this as Theorem 5.8, p.28, where it is proved. It is the first clause of the main theorem.
--
--   Differences from the source:
--   - encoding: $U\subseteq\mathcal H_K$ open in the subspace $\mathcal H_K$ → $U$ open in the space of all histories and contained in $\mathcal H_K$; reason: $\mathcal H_K$ is open and closed (p.27), so the two agree
--   - encoding: a countable rooted tree with no infinite path → the inductive type `ObsTree` with `ℕ`-indexed children; reason: same trees up to repeated subtrees, which do not change the path set
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Theorem 2.6, eq. (10), p.17; restated as Theorem 5.8, p.28

import Mathlib
import Definitions.Def_LocalBreadth_bComb
import Definitions.Def_LocalBreadth_bTop

namespace LocalBreadth

/-- Theorem 2.6. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), eq. (10), p.17;
restated as Theorem 5.8, p.28. For every `K ∈ X` and every positive integer `n`,
`b_n(K) = sup_{U ⊆ ℋ_K open, (K) ∈ U} inf_{H ∈ U} c_n(H)`. -/
theorem theorem_2_6 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite) :
    ∀ K ∈ X, ∀ n : ℕ, 1 ≤ n → bComb X n K = bTop X n K := by sorry

end LocalBreadth
