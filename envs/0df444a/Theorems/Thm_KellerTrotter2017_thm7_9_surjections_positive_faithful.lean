-- Prove2me | Theorems.Thm_KellerTrotter2017_thm7_9_surjections_positive_faithful
-- name    : KellerTrotter2017.thm7_9_surjections_positive_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:26:53.315016+00:00
-- url     : https://prove2.me/theorems/06f5df8c-607a-4aad-b6f7-a64986ff74bf
-- title:
--   Theorem 7.9 (number of surjections), for positive $n, m$ as in the book
-- statement:
--   Let $n$ and $m$ be positive integers and let $S(n,m)$ denote the number of surjections from $[n] = \{1, \dots, n\}$ onto $[m] = \{1, \dots, m\}$. Then
--
--   $$S(n,m) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (m-k)^n.$$
--
--   This is Theorem 7.9 of Keller and Trotter, *Applied Combinatorics*, exactly as stated there, for positive $n$ and $m$. The existing theorem AppliedComb.InclExcl.surjections_count proves the same identity for all $n, m \ge 0$.
--
--   **Formalization Note** $[n]$ is represented by `Fin n`; the identity is stated in $\mathbb Z$, with $m - k$ computed in $\mathbb N$ (exact since $k \le m$) and cast.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 146, Theorem 7.9

import Mathlib

theorem KellerTrotter2017.thm7_9_surjections_positive_faithful (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (Fintype.card {f : Fin n → Fin m // Function.Surjective f} : ℤ) =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ k * (m.choose k : ℤ) * ((m - k : ℕ) : ℤ) ^ n := by sorry
