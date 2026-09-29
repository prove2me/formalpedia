-- Prove2me | Theorems.Thm_LogRegretOCO_EWOO_ewoo_regret_bound
-- name    : LogRegretOCO.EWOO.ewoo_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:47:02.531371+00:00
-- url     : https://prove2.me/theorems/c2dd4fb1-0afc-4c18-bc92-43659837625f
-- title:
--   Theorem 7: Regret_T(EWOO) ≤ (1/α) n (1 + log(T + 1)) on α-exp-concave costs
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be a nonempty, closed, bounded, convex set of positive Lebesgue volume, and let $\alpha > 0$. Let $f_1, f_2, \dots : \mathbb{R}^n \to \mathbb{R}$ be cost functions that are continuous on $P$ and **$\alpha$-exp-concave** on $P$, i.e. $x \mapsto e^{-\alpha f_t(x)}$ is concave on $P$ for every $t$. Let $x_1, x_2, \dots$ be the points played by **Exponentially Weighted Online Optimization**,
--
--   $$
--   x_t = \frac{\int_P x\, w_t(x)\, dx}{\int_P w_t(x)\, dx}, \qquad w_t(x) = \exp\Bigl(-\alpha \sum_{\tau=1}^{t-1} f_\tau(x)\Bigr).
--   $$
--
--   Then for every horizon $T \ge 1$ and every comparator $u \in P$,
--
--   $$
--   \sum_{t=1}^{T} f_t(x_t) - \sum_{t=1}^{T} f_t(u) \;\le\; \frac{1}{\alpha}\, n\, \bigl(1 + \log(T+1)\bigr).
--   $$
--
--   Since the bound holds for every $u \in P$, it bounds the regret $\sum_t f_t(x_t) - \min_{x \in P} \sum_t f_t(x)$, uniformly over all cost sequences, including those chosen adaptively. The bound is logarithmic in $T$ and, unlike the bounds for the Online Newton Step and Follow the Approximate Leader, involves neither a gradient bound nor the diameter of $P$.
--
--   **Formalization Note** The regret is stated against every comparator $u \in P$ rather than through a real-valued minimum, which is the same statement because the minimum is attained on the compact set $P$. Positive volume of $P$ is presupposed by the algorithm (it divides by $\int_P w_t$). Continuity of each $f_t$ on $P$ is the paper's standing assumption (§2.2: costs twice differentiable and convex) weakened to what is needed for the integrals to be meaningful. The paper's "$f_t : P \to \mathbb{R}^n$" is a typo for real-valued costs. The paper's proof gives the sharper bound $\frac{1}{\alpha}(1 + n\log(T+1))$; the printed constant is stated.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 186, Theorem 7 ("Assume that for all t, the function f_t : P → ℝ^n has the property that ∀x ∈ P, exp(−αf(x)) is concave. Then the algorithm EXPONENTIALLY WEIGHTED ONLINE OPTIMIZATION has the following regret bound: Regret_T(EWOO) ≤ 1/α n(1 + log(T + 1))."); algorithm Fig. 4, p. 186; standing assumptions §2.1–2.2, pp. 171–173

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- Theorem 7 (Hazan–Agarwal–Kale 2007, p. 186): on a nonempty, closed, bounded, convex
`P ⊆ ℝⁿ` of positive volume, with `α > 0` and every `f_t` α-exp-concave and continuous on `P`,
the points `x_t` of EXPONENTIALLY WEIGHTED ONLINE OPTIMIZATION satisfy, for every `T ≥ 1` and
every comparator `u ∈ P`,
`∑_{t=1}^T (f_t(x_t) − f_t(u)) ≤ (1/α) n (1 + log(T + 1))`. -/
theorem ewoo_regret_bound (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (T : ℕ) (hT : 1 ≤ T) (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ P) :
    ∑ t ∈ Finset.Icc 1 T, (f t (ewooPoint P α f t) - f t u)
      ≤ 1 / α * n * (1 + Real.log ((T : ℝ) + 1)) := by sorry

end LogRegretOCO.EWOO
