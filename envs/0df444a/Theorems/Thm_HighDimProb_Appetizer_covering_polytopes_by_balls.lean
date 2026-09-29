-- Prove2me | Theorems.Thm_HighDimProb_Appetizer_covering_polytopes_by_balls
-- name    : HighDimProb.Appetizer.covering_polytopes_by_balls
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:34:37.656979+00:00
-- url     : https://prove2.me/theorems/7bce09a5-1f37-464d-88d1-362039f33cf8
-- title:
--   Corollary 0.0.4 — Covering polytopes by balls
-- statement:
--   This is the **covering-polytopes-by-balls** corollary of the approximate Carathéodory
--   theorem, an application to the covering problem in computational geometry.
--
--   Let $P \subseteq \mathbb{R}^n$ be a polytope of diameter at most $1$ (in the Euclidean
--   norm), presented as the convex hull of its finite vertex set $T$ with $|T| = N$ — this is
--   how the book itself identifies "a polytope with $N$ vertices" with $P = \operatorname{conv}(T)$.
--   Fix a radius $\varepsilon > 0$ and set $k := \lceil 1/\varepsilon^2 \rceil$. The corollary
--   asserts that there is a finite set of centers $C \subseteq \mathbb{R}^n$ with
--
--   $$
--   |C| \le N^{\lceil 1/\varepsilon^2 \rceil}
--   $$
--
--   such that $P$ is covered by the Euclidean balls of radius $\varepsilon$ centered at the
--   points of $C$:
--
--   $$
--   P \subseteq \bigcup_{c \in C} \overline{B}(c, \varepsilon).
--   $$
--
--   The centers are taken to be all averages of $k$ vertices of $P$ (with repetition), so
--   $|C|$ is bounded by the number $N^k$ of such $k$-tuples; the approximate Carathéodory
--   theorem (Theorem 0.0.2) guarantees that every point of $P = \operatorname{conv}(T)$ lies
--   within $1/\sqrt{k} \le \varepsilon$ of one of these averages, hence within one of the
--   balls. This gives a covering bound for polytopes that depends only on the number of
--   vertices $N$ and the target accuracy $\varepsilon$, not on the ambient dimension $n$.
--
--   **Formalization Note** As in Theorem 0.0.2, `EuclideanSpace ℝ (Fin n)` carries the
--   Euclidean norm and Mathlib's `Metric.diam`/`Metric.closedBall`. The exponent
--   $\lceil 1/\varepsilon^2 \rceil$ is Mathlib's `Nat.ceil`, written `⌈(1:ℝ)/ε^2⌉₊`. The bound
--   on the right is $N$ raised to the power $\lceil 1/\varepsilon^2\rceil$ (matching the
--   book's proof, which counts ordered $k$-tuples of vertices with repetition), not a product
--   $N\cdot\lceil 1/\varepsilon^2\rceil$ — the typeset "$N\lceil 1/\varepsilon^2\rceil$" in the
--   corollary's statement is the same juxtaposition-as-exponent the book uses for "$N^k$" two
--   lines earlier in its own proof.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Corollary 0.0.4, p. 3 (PDF p. 11)

import Mathlib

namespace HighDimProb.Appetizer

/-- **Corollary 0.0.4** (Covering polytopes by balls), Vershynin,
*High-Dimensional Probability* (2018), p. 3.

Let `P` be a polytope in `ℝⁿ` with `N` vertices and whose diameter is bounded
by `1`; identify `P` with the convex hull of its finite vertex set `T`
(`#T = N`), exactly as the book's own proof does. Then `P` can be covered by
at most `N ^ ⌈1/ε²⌉` Euclidean balls of radius `ε > 0`. -/
theorem covering_polytopes_by_balls {n N : ℕ} (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hTcard : T.card = N) (hTdiam : Metric.diam (T : Set (EuclideanSpace ℝ (Fin n))) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ centers : Finset (EuclideanSpace ℝ (Fin n)),
      centers.card ≤ N ^ ⌈(1 : ℝ) / ε ^ 2⌉₊ ∧
      convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin n))) ⊆
        ⋃ c ∈ centers, Metric.closedBall c ε := by sorry

end HighDimProb.Appetizer
