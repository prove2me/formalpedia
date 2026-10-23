-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_corollary_5_a
-- name    : LargeCongestion.Poisson.corollary_5_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:31.312794+00:00
-- url     : https://prove2.me/theorems/93573d43-458c-42c7-9259-947bcbe5de2b
-- title:
--   Corollary 5(a), p. 38 — if E[|Δ²h(V)|] ≤ ν < ∞, then |h̆′(x)| ≤ (e^{d_max} − 1)ν + |h(1) − h(0)| on [0, d_max]
-- statement:
--   Let $h : \mathbb N \to \mathbb R$, $d_{\max} > 0$, $V \sim \mathrm{Poisson}(d_{\max})$, and suppose $\mathsf E[|\Delta^2 h(V)|] \le \nu < \infty$. Then for all $x \in [0, d_{\max}]$,
--   $$|\breve h'(x)| \le (e^{d_{\max}} - 1)\,\nu + |h(1) - h(0)| .$$
--
--   This Lipschitz bound on the Poisson mixture is the source of the constant $\zeta$ in (19).
--
--   **Formalization Note** The expectation in the hypothesis is required to be a convergent series, and $\breve h'$ is the derivative within $[0, d_{\max}]$.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 38, Appendix C, Corollary 5(a)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory

/-- Corollary 5(a), Appendix C, p. 38: if `E[|Δ²h(V)|] ≤ ν < ∞` for `V ∼ Poisson(d_max)`, then
`|h̆′(x)| ≤ (e^{d_max} − 1) ν + |h(1) − h(0)|` for all `x ∈ [0, d_max]`. -/
theorem corollary_5_a (h : ℕ → ℝ) (dmax ν : ℝ) (hd : 0 < dmax)
    (hint : Summable (fun k : ℕ => |deltaPow 2 h k| * poissonPmf dmax k))
    (hν : ∑' k : ℕ, |deltaPow 2 h k| * poissonPmf dmax k ≤ ν) :
    ∀ x ∈ Set.Icc 0 dmax,
      |derivWithin (poissonMean h) (Set.Icc 0 dmax) x| ≤
        (Real.exp dmax - 1) * ν + |h 1 - h 0| := by sorry

end LargeCongestion.Poisson
