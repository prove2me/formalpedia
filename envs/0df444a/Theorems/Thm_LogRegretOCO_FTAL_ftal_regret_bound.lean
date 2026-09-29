-- Prove2me | Theorems.Thm_LogRegretOCO_FTAL_ftal_regret_bound
-- name    : LogRegretOCO.FTAL.ftal_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:41:59.457275+00:00
-- url     : https://prove2.me/theorems/7738fd0f-d5ad-41b5-bc28-32437dfdedaf
-- title:
--   Theorem 6 — Follow the Approximate Leader has regret at most $64(1/\alpha + GD)\, n(\log T + 1)$
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be nonempty, convex, closed and bounded, with $\|y - z\| \le D$ for all $y, z \in P$, where $D > 0$. Let $f_1, f_2, \dots$ be cost functions, each differentiable at every point of $P$, such that for some $G > 0$ and $\alpha > 0$ and every round $t \ge 1$:
--
--   1. $\|\nabla f_t(x)\| \le G$ for all $x \in P$;
--   2. $x \mapsto \exp(-\alpha f_t(x))$ is concave on $P$ ($f_t$ is $\alpha$-exp-concave).
--
--   Let $x_1, x_2, \dots$ be a run of Follow the Approximate Leader (version 1) with parameter
--
--   $$
--   \beta = \frac12 \min\left\{\frac{1}{4GD}, \alpha\right\}.
--   $$
--
--   Then for every horizon $T \ge 1$ and every comparator $u \in P$,
--
--   $$
--   \sum_{t=1}^T \bigl(f_t(x_t) - f_t(u)\bigr) \le 64\left(\frac1\alpha + GD\right) n \,(\log T + 1).
--   $$
--
--   This is the paper's logarithmic regret guarantee for Follow the Approximate Leader: against any sequence of $\alpha$-exp-concave costs chosen by an adversary, the algorithm's total cost exceeds that of the best fixed decision in hindsight by $O(n \log T)$.
--
--   **Formalization Note** The paper writes "$f_t : P \to \mathbb{R}^n$", a typo for $\mathbb{R}$, and assumes the costs twice differentiable; only first-order differentiability at the points of $P$ is assumed here (the result is correspondingly stronger). The costs are functions on all of $\mathbb{R}^n$ and the gradient is Mathlib's `gradient`. $D$ is any upper bound on the diameter of $P$. $G > 0$, $D > 0$ are required because $\beta$ divides by $GD$ (in Lean $1/0 = 0$). The minimum in the paper's regret is replaced by "for every $u \in P$", which is equivalent since $P$ is compact. The statement is true as printed, although its proof in the paper passes through the printed Theorem 5, which is invalid for $T < 16$ in this application; the corrected Theorem 5 of this mission yields the printed constant for all $T \ge 1$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 182, Theorem 6 (proof pp. 182–183)

import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTALRun

namespace LogRegretOCO.FTAL
theorem ftal_regret_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (D G α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (hPclosed : IsClosed P)
    (hPbdd : Bornology.IsBounded P)
    (hD : 0 < D) (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hG : 0 < G) (hα : 0 < α)
    (hdiff : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (f t) y)
    (hgrad : ∀ t, 1 ≤ t → ∀ y ∈ P, ‖gradient (f t) y‖ ≤ G)
    (hexp : ∀ t, 1 ≤ t → ConcaveOn ℝ P (fun y => Real.exp (-α * f t y)))
    (hx : IsFTALRun P (1 / 2 * min (1 / (4 * G * D)) α) f x) :
    ∀ T : ℕ, 1 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u)
        ≤ 64 * (1 / α + G * D) * n * (Real.log T + 1) := by sorry
end LogRegretOCO.FTAL
