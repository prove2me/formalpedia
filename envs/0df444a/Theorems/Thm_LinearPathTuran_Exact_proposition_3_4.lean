-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_proposition_3_4
-- name    : LinearPathTuran.Exact.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:28.926732+00:00
-- url     : https://prove2.me/theorems/53fa08d1-8730-4c46-a42a-91898cbb3f17
-- title:
--   Proposition 3.4 (the rank bound) — a (k,s)-homogeneous family whose pattern has rank p has at most C(n,p) members
-- statement:
--   **The rank bound.** Let $k,s$ be positive integers and let $\mathcal F^*$ be a $(k,s)$-homogeneous family on $n$ vertices with intersection pattern $\mathcal J$. If $r(\mathcal J)=p$, then
--   $$|\mathcal F^*|\le\binom{n}{p}.$$
--
--   This is why only homogeneous pieces whose pattern has rank $k-1$ or $k$ can carry $\Theta(n^{k-1})$ members; pieces of rank at most $k-2$ contribute $O(n^{k-2})$.
--
--   **Formalization Note** The rank is the minimum size of a subset of $[k]$ contained in no member of $\mathcal J$; since the members of $\mathcal J$ are proper subsets of $[k]$ this minimum exists.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 5, Proposition 3.4

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Proposition 3.4 (the rank bound), p. 5. -/
theorem proposition_3_4 (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (χ : Fin n → Fin k) (J : Finset (Finset (Fin k)))
    (hH : IsHomogeneous s 𝓕 χ J) (p : ℕ) (hp : rank J = p) :
    #𝓕 ≤ n.choose p := by sorry

end LinearPathTuran.Exact
