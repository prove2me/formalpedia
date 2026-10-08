-- Prove2me | Theorems.Thm_MatousekLP_DIntervals_exists_endpoint_in_many
-- name    : MatousekLP.DIntervals.exists_endpoint_in_many
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T14:01:44.149032+00:00
-- url     : https://prove2.me/theorems/fa915da9-f3bd-47b7-8593-dac0fd38fa73
-- title:
--   Lemma 8.6.2 — some endpoint lies in at least n/2d of n pairwise intersecting d-intervals
-- statement:
--   Let $d \ge 1$ and $n \ge 1$, and let $J_1, J_2, \dots, J_n$ be $d$-intervals (a finite *sequence*, so repetitions are allowed) such that $J_i \cap J_j \ne \emptyset$ for all $i, j \in \{1,\dots,n\}$. Then there is an index $i$ and an endpoint $p$ of $J_i$ such that
--   $$
--   \bigl|\{\, j \in \{1,\dots,n\} : p \in J_j \,\}\bigr| \;\ge\; \frac{n}{2d}.
--   $$
--
--   This is the counting step behind the section's capstone: in a pairwise intersecting sequence, a single endpoint is covered by a fixed fraction $1/2d$ of the members. Allowing repetitions is what later lets rational weights be replaced by multiplicities.
--
--   **Formalization Note** The sequence is indexed by `Fin n` (the book's $1,\dots,n$ are `0, …, n-1`). The count is the number of indices $j$, counted with repetitions, and $n/2d$ is real division. The hypothesis $n \ge 1$ is implicit in the book's $J_1,\dots,J_n$ and is stated explicitly, since with $n = 0$ there is no endpoint at all.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 179, Lemma 8.6.2

import Mathlib
import Definitions.Def_MatousekLP_DIntervals_DInterval

open Finset

namespace MatousekLP.DIntervals

open Classical in
/-- Lemma 8.6.2 (p. 179): if `J_1, …, J_n` (`n ≥ 1`, repetitions allowed) are `d`-intervals with
`J_i ∩ J_j ≠ ∅` for all `i, j`, then some endpoint `p` of some `J_i` lies in at least `n / 2d`
of the `J_j`. Indices `1, …, n` are `0, …, n-1`. -/
theorem exists_endpoint_in_many {d n : ℕ} (hd : 1 ≤ d) (hn : 0 < n) (J : Fin n → DInterval d)
    (hJ : ∀ i j, ((J i).toSet ∩ (J j).toSet).Nonempty) :
    ∃ i : Fin n, ∃ p ∈ (J i).endpoints,
      (n : ℝ) / (2 * d) ≤ ((univ.filter fun j => p ∈ (J j).toSet).card : ℝ) := by sorry

end MatousekLP.DIntervals
