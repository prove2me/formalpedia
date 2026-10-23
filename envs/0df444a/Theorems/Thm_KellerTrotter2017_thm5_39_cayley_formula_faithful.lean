-- Prove2me | Theorems.Thm_KellerTrotter2017_thm5_39_cayley_formula_faithful
-- name    : KellerTrotter2017.thm5_39_cayley_formula_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:26:53.698427+00:00
-- url     : https://prove2.me/theorems/ab510481-8872-4008-beb2-2ac62e71a9f9
-- title:
--   Theorem 5.39 — Cayley's Formula $T_n = n^{n-2}$
-- statement:
--   Let $n \ge 1$ and let $T_n$ be the number of trees with vertex set $[n] = \{1, \dots, n\}$ (labeled trees on $n$ vertices). Then
--
--   $$T_n = n^{\,n-2}.$$
--
--   This is Theorem 5.39 (Cayley's Formula) of Keller and Trotter, *Applied Combinatorics*, proved there with Prüfer codes.
--
--   **Formalization Note** A labeled tree is a simple graph on `Fin n` that is a tree; for $n = 1$ the exponent $n - 2$ is computed in $\mathbb N$ and equals $0$, matching $1^{-1} = 1$. The case $n = 0$ is excluded: there is no tree on the empty vertex set.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 97, Theorem 5.39

import Mathlib

theorem KellerTrotter2017.thm5_39_cayley_formula_faithful (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {G : SimpleGraph (Fin n) // G.IsTree} = n ^ (n - 2) := by sorry
