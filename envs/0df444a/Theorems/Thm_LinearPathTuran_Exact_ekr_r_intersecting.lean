-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_ekr_r_intersecting
-- name    : LinearPathTuran.Exact.ekr_r_intersecting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:55.09532+00:00
-- url     : https://prove2.me/theorems/712f1ae5-4a0e-4441-a24c-0eccb64b1768
-- title:
--   §5, p. 12 — r-intersecting Erdős–Ko–Rado for large n: the unique largest family is a full r-star
-- statement:
--   **The $r$-intersecting Erdős–Ko–Rado theorem.** Let $1\le r\le k$. There is $n(k,r)$ such that for every $n>n(k,r)$: if $\mathcal F\subseteq\binom{[n]}{k}$ is $r$-intersecting (every two members share at least $r$ elements), then
--   $$|\mathcal F|\le\binom{n-r}{k-r},$$
--   with equality only if $\mathcal F$ is the family of all $k$-subsets of $[n]$ containing some fixed $r$-set $R$.
--
--   The paper applies it with $r=2$ to the members disjoint from $S$ in the even case (equation (8)).
--
--   **Formalization Note** "Every two members" is checked for all pairs, including a member with itself; this is harmless since $|A\cap A|=k\ge r$. The equality clause is an equivalence, which also records that the full $r$-star attains the bound. The theorem is cited from Erdős, Ko and Rado (1961).
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 12, §5, "Erdős-Ko-Rado [7] showed that for fixed k and large n the unique largest r-intersecting family …" (cited from Erdős, Ko and Rado, Quart. J. Math. Oxford 12 (1961))

import Mathlib

namespace LinearPathTuran.Exact

open Finset

/-- The `r`-intersecting Erdős–Ko–Rado theorem for large `n` (cited on p. 12): the unique largest
`r`-intersecting `k`-uniform family on `[n]` is the family of all `k`-sets through a fixed `r`-set. -/
theorem ekr_r_intersecting (k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) :
    ∃ n₀ : ℕ, ∀ n > n₀, ∀ 𝓕 : Finset (Finset (Fin n)),
      𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k →
      (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, r ≤ #(A ∩ B)) →
      #𝓕 ≤ (n - r).choose (k - r) ∧
      (#𝓕 = (n - r).choose (k - r) ↔
        ∃ R : Finset (Fin n), #R = r ∧
          𝓕 = ((univ : Finset (Fin n)).powersetCard k).filter (fun A => R ⊆ A)) := by sorry

end LinearPathTuran.Exact
