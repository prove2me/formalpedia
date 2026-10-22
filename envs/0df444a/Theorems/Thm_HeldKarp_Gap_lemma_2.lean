-- Prove2me | Theorems.Thm_HeldKarp_Gap_lemma_2
-- name    : HeldKarp.Gap.lemma_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:07.43721+00:00
-- url     : https://prove2.me/theorems/835c2e81-4804-4a99-93d9-4b6c72340269
-- title:
--   Lemma 2 — the degree constraints (i) of (3) may be replaced by degree 2 at $1,\dots,n-1$ and $\sum x_{ij}=n$
-- statement:
--   Let $n\ge 3$ and let $x=(x_{ij})_{1\le i<j\le n}$ be any real $\binom n2$-vector. Then $x$ satisfies the degree constraints (i) of program (3),
--
--   $$
--   \sum_{j>i}x_{ij}+\sum_{j<i}x_{ji}=2\qquad(i=1,2,\dots,n),
--   $$
--
--   if and only if it satisfies
--
--   $$
--   \sum_{j>i}x_{ij}+\sum_{j<i}x_{ji}=2\quad(i=1,2,\dots,n-1)\qquad\text{and}\qquad \sum_{1\le i<j\le n}x_{ij}=n.
--   $$
--
--   Hence in program (3) the constraints (i) may be replaced by these, which gives program (3′); since the replacement is valid for every real vector, the same holds for the linear relaxation (4).
--
--   **Formalization Note** The paper states the lemma for program (3); the formal statement is the constraint-by-constraint equivalence for every real vector (no other constraint of (3) is assumed), which is what the paper's proof shows. Vectors are functions on unordered pairs $\{i,j\}$, $i\ne j$, of `Fin n`; the paper's vertex $n$ is the last element `lastV n`.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, p. 1143, §2, Lemma 2

import Mathlib
import Definitions.Def_HeldKarp_Gap_SubtourLP

open Classical

namespace HeldKarp.Gap

/-- **Lemma 2** (Held & Karp 1970, §2, p. 1143). In program (3) the constraints (i) (degree 2 at
every vertex `i = 1, …, n`) may be replaced by degree 2 at `i = 1, …, n − 1` together with
`Σ_{1≤i<j≤n} x_ij = n`. Stated constraint by constraint, for every real `(n choose 2)`-vector. -/
theorem lemma_2 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : Edge n → ℝ) :
    (∀ i : Fin n, deg x i = 2) ↔
      ((∀ i : Fin n, i ≠ lastV n → deg x i = 2) ∧ total x = n) := by sorry

end HeldKarp.Gap
