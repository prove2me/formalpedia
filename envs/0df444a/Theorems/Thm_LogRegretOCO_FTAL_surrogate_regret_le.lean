-- Prove2me | Theorems.Thm_LogRegretOCO_FTAL_surrogate_regret_le
-- name    : LogRegretOCO.FTAL.surrogate_regret_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:39:18.847109+00:00
-- url     : https://prove2.me/theorems/a60977e7-f32c-492a-8f3b-05427a170149
-- title:
--   Lemma 9 — regret on lower surrogates dominates the true regret
-- statement:
--   Let $f_1, \dots, f_T$ and $\tilde f_1, \dots, \tilde f_T$ be cost functions and let $x_1, \dots, x_T \in P$ be the points played. Suppose that for each round $t$ the surrogate touches the cost at the played point and lies below it on $P$:
--
--   $$
--   f_t(x_t) = \tilde f_t(x_t), \qquad f_t(x) \ge \tilde f_t(x) \quad \text{for all } x \in P.
--   $$
--
--   Then for every comparator $u \in P$,
--
--   $$
--   \sum_{t=1}^T f_t(x_t) - \sum_{t=1}^T f_t(u) \le \sum_{t=1}^T \tilde f_t(x_t) - \sum_{t=1}^T \tilde f_t(u).
--   $$
--
--   Taking the maximum over $u$ on the left and bounding the right by its maximum over $u$ gives the paper's form: the regret on the true costs is at most the regret on the surrogates. This reduces the analysis of Follow the Approximate Leader to Follow the Leader on quadratic surrogates.
--
--   **Formalization Note** The paper writes regret with $\min_{x \in P}$; here it is stated against every comparator $u \in P$, which is equivalent and avoids a real-valued infimum (which Lean sets to $0$ on unbounded sets). Rounds are $1$-based.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 189, Lemma 9 (Appendix 1)

import Mathlib

namespace LogRegretOCO.FTAL
theorem surrogate_regret_le {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f fT : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (T : ℕ)
    (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ P)
    (heq : ∀ t ∈ Finset.Icc 1 T, f t (x t) = fT t (x t))
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ y ∈ P, fT t y ≤ f t y) :
    ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t u
        ≤ ∑ t ∈ Finset.Icc 1 T, fT t (x t) - ∑ t ∈ Finset.Icc 1 T, fT t u := by sorry
end LogRegretOCO.FTAL
