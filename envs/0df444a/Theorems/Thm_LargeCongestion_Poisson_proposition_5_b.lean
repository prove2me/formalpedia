-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_proposition_5_b
-- name    : LargeCongestion.Poisson.proposition_5_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:38.916185+00:00
-- url     : https://prove2.me/theorems/f258fa68-6324-43c6-8958-7566cde0112c
-- title:
--   Proposition 5(b), p. 37 — E[|Δ^j h(X)|] < ∞ ⟺ E[|h(X + j)|] < ∞ ⟺ E[X^j |h(X)|] < ∞
-- statement:
--   Let $h : \mathbb N \to \mathbb R$, $x \ge 0$ and $X \sim \mathrm{Poisson}(x)$. For each $j = 1, 2, \dots$,
--   $$\mathsf E[|\Delta^j h(X)|] < \infty \iff \mathsf E[|h(X + j)|] < \infty \iff \mathsf E[X^j|h(X)|] < \infty .$$
--
--   These equivalences translate integrability of differences of $h$, the form in which condition (18) is stated, into integrability of shifted values of $h$, which is what differentiating $\breve h$ requires.
--
--   **Formalization Note** Each expectation $\mathsf E[|g(X)|] < \infty$ is the summability of $k \mapsto |g(k)|\,\mathsf P(X = k)$.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 37, Appendix C, Proposition 5(b)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory

/-- Proposition 5(b), Appendix C, p. 37: for `X ∼ Poisson(x)` and `j = 1, 2, …`,
`E[|Δ^j h(X)|] < ∞ ⟺ E[|h(X + j)|] < ∞ ⟺ E[X^j |h(X)|] < ∞`. -/
theorem proposition_5_b (h : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (hj : 1 ≤ j) :
    (Summable (fun k : ℕ => |deltaPow j h k| * poissonPmf x k) ↔
        Summable (fun k : ℕ => |h (k + j)| * poissonPmf x k)) ∧
      (Summable (fun k : ℕ => |h (k + j)| * poissonPmf x k) ↔
        Summable (fun k : ℕ => (k : ℝ) ^ j * |h k| * poissonPmf x k)) := by sorry

end LargeCongestion.Poisson
