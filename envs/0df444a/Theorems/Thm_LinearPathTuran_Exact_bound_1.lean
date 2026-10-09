-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_bound_1
-- name    : LinearPathTuran.Exact.bound_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:45.754419+00:00
-- url     : https://prove2.me/theorems/ece4243d-4e82-4150-b8d1-a488fc604af1
-- title:
--   Bound (1) — ex_k(n, ℙ_ℓ) ≤ (k−1)(ℓ−1)·C(n−1, k−1) for every n
-- statement:
--   Let $k\ge 2$ and $\ell\ge 1$. For every $n$,
--   $$\mathbf{ex}_k(n,\mathbb P^{(k)}_\ell)\le(k-1)(\ell-1)\binom{n-1}{k-1}.$$
--
--   It is weaker than Theorem 4.5 for large $n$ but holds for every $n$; §5 applies it to the family of members inside the small exceptional set $Z$ (equation (4)).
--
--   **Formalization Note** The page states the bound inside §4, whose results assume $k\ge4$, without restricting $k$; it is posed here for $k\ge 2$, where the degree-removal argument the page refers to works. For $k=1$ it is false ($n$ singletons contain no $\mathbb P_2^{(1)}$), so $k\ge2$ is needed. Natural-number subtractions $k-1$, $\ell-1$, $n-1$ are exact for $k\ge2$, $\ell\ge1$, $n\ge1$, and both sides are $0$ at $n=0$.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 9, equation (1)

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_Setting

namespace LinearPathTuran.Exact

open Finset

/-- Bound (1), p. 9: `ex_k(n, ℙ_ℓ) ≤ (k - 1)(ℓ - 1) C(n - 1, k - 1)` for every `n`. -/
theorem bound_1 (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (n : ℕ) :
    exLin n k ℓ ≤ (k - 1) * (ℓ - 1) * (n - 1).choose (k - 1) := by sorry

end LinearPathTuran.Exact
