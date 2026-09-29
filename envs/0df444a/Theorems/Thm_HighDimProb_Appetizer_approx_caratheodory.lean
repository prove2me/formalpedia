-- Prove2me | Theorems.Thm_HighDimProb_Appetizer_approx_caratheodory
-- name    : HighDimProb.Appetizer.approx_caratheodory
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:34:15.668993+00:00
-- url     : https://prove2.me/theorems/779cf296-78b5-4176-96f9-a9c60813c82f
-- title:
--   Theorem 0.0.2 — Approximate Carathéodory's theorem
-- statement:
--   This is the **approximate Carathéodory theorem** — B. Maurey's "empirical method" — for
--   a bounded subset of Euclidean space.
--
--   Let $T \subseteq \mathbb{R}^n$ be a set of diameter at most $1$ (in the Euclidean norm
--   $\|\cdot\|_2$), and let $\operatorname{conv}(T)$ denote its convex hull: the set of all
--   finite convex combinations of points of $T$. Fix a point $x \in \operatorname{conv}(T)$
--   and a positive integer $k$. The theorem asserts that there exist points
--   $x_1, \dots, x_k \in T$ (repetitions among the $x_j$ are allowed) such that
--
--   $$
--   \left\| x - \frac{1}{k}\sum_{j=1}^{k} x_j \right\|_2 \le \frac{1}{\sqrt{k}}.
--   $$
--
--   In other words, $x$ can be approximated by the average of $k$ points of $T$, to accuracy
--   $1/\sqrt{k}$, with **all coefficients equal** to $1/k$. Two features make this surprising
--   when compared with the classical (exact) Carathéodory theorem: the number of points $k$
--   needed for a given accuracy does not depend on the ambient dimension $n$ at all, and the
--   convex-combination coefficients can be taken uniform rather than arbitrary nonnegative
--   weights summing to one.
--
--   The result underlies the probabilistic ("empirical") method throughout high-dimensional
--   probability: $x$ is realized as the expectation of a random vector supported on $T$, and
--   an averaged sample of $k$ independent copies concentrates around its mean at rate
--   $1/\sqrt{k}$ by a variance (weak-law-of-large-numbers) computation.
--
--   **Formalization Note** $T$ is a subset of `EuclideanSpace ℝ (Fin n)` for an explicit
--   `n : ℕ`, so `‖·‖` is the Euclidean ($\ell^2$) norm and `Metric.diam` is Mathlib's diameter,
--   which for this space agrees with $\operatorname{diam}(T) = \sup\{\|s-t\|_2 : s,t\in T\}$.
--   `conv(T)` is Mathlib's `convexHull ℝ T`; by `convexHull_eq` this already unfolds to the
--   book's own definition (Eq. 0.1) of a convex combination of finitely many points of $T$, so
--   no separate definition is introduced. The quantifiers are exactly the book's: for every
--   $T$, every $x \in \operatorname{conv}(T)$, and every $k > 0$ (the hypothesis $k>0$ makes
--   $1/k$ and $1/\sqrt k$ meaningful; the book's "every integer $k$" is implicitly positive).
--   The book's "diameter bounded by $1$" is rendered as two hypotheses, `Bornology.IsBounded T`
--   and `Metric.diam T ≤ 1`, because Mathlib's `Metric.diam` returns $0$ on unbounded sets; without
--   the boundedness hypothesis the statement would also assert the conclusion for unbounded $T$,
--   where it is false.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 0.0.2, p. 2 (PDF p. 10)

import Mathlib

namespace HighDimProb.Appetizer

/-- **Theorem 0.0.2** (Approximate Carathéodory's theorem), Vershynin,
*High-Dimensional Probability* (2018), p. 2.

Consider a set `T ⊆ ℝⁿ` whose diameter is bounded by `1` (so `T` is bounded and
`diam T ≤ 1`; Mathlib's `Metric.diam` is `0` on unbounded sets, hence the explicit
boundedness hypothesis). Then, for every point
`x ∈ conv(T)` and every positive integer `k`, one can find points
`x₁, …, x_k ∈ T` such that `‖x − (1/k) ∑ⱼ xⱼ‖₂ ≤ 1/√k`. -/
theorem approx_caratheodory {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n)))
    (hTb : Bornology.IsBounded T) (hT : Metric.diam T ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ convexHull ℝ T)
    (k : ℕ) (hk : 0 < k) :
    ∃ x' : Fin k → EuclideanSpace ℝ (Fin n), (∀ j, x' j ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • ∑ j, x' j‖ ≤ 1 / Real.sqrt k := by sorry

end HighDimProb.Appetizer
