-- Prove2me | Theorems.Thm_LogRegretOCO_EWOO_jensen_weighted_mean
-- name    : LogRegretOCO.EWOO.jensen_weighted_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:43:48.255788+00:00
-- url     : https://prove2.me/theorems/3f779b96-091b-4b7b-a224-7d7c9dde707c
-- title:
--   §3.4 (p. 187): h_t(x_t) ≥ ∫_P h_t ∏_{τ<t} h_τ / ∫_P ∏_{τ<t} h_τ for the EWOO point
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be nonempty, closed, bounded and convex with positive Lebesgue volume, let $\alpha > 0$, and let $f_1, f_2, \dots : \mathbb{R}^n \to \mathbb{R}$ be continuous on $P$ and $\alpha$-exp-concave on $P$. Write $h_\tau(x) = e^{-\alpha f_\tau(x)}$ and let $x_t$ be the point played by Exponentially Weighted Online Optimization on round $t$. Then for every round $t \ge 1$,
--
--   $$
--   h_t(x_t) \;\ge\; \frac{\int_P h_t(x) \prod_{\tau=1}^{t-1} h_\tau(x)\, dx}{\int_P \prod_{\tau=1}^{t-1} h_\tau(x)\, dx}.
--   $$
--
--   Since $\prod_{\tau=1}^{t-1} h_\tau = w_t$ is the EWOO weight, $x_t$ is the mean of $P$ under the probability density proportional to $w_t$, and the inequality is Jensen's inequality for the concave function $h_t$ under that distribution. It is the per-round step from which Eq. (18) follows by multiplying over rounds.
--
--   **Formalization Note** Continuity of $f_t$ on $P$ is the part of the paper's standing assumption (§2.2: the costs are twice differentiable and convex) that the argument uses; it makes every integral here a genuine (integrable) integral. Positive volume of $P$ is presupposed by the algorithm, which divides by $\int_P w_t$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 187, §3.4, proof of Theorem 7, first display on p. 187

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- §3.4, first display on p. 187 (Hazan–Agarwal–Kale 2007): for `h_t(x) = exp(-α f_t(x))`,
the EWOO point satisfies
`h_t(x_t) ≥ ∫_P h_t(x) ∏_{τ=1}^{t-1} h_τ(x) dx / ∫_P ∏_{τ=1}^{t-1} h_τ(x) dx`. -/
theorem jensen_weighted_mean (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (t : ℕ) (ht : 1 ≤ t) :
    (∫ x in P, Real.exp (-α * f t x) * ∏ τ ∈ Finset.Ico 1 t, Real.exp (-α * f τ x)) /
        (∫ x in P, ∏ τ ∈ Finset.Ico 1 t, Real.exp (-α * f τ x))
      ≤ Real.exp (-α * f t (ewooPoint P α f t)) := by sorry

end LogRegretOCO.EWOO
