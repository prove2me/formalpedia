-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_proposition_6_b
-- name    : LargeCongestion.Poisson.proposition_6_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:33.272776+00:00
-- url     : https://prove2.me/theorems/f0e6306e-5530-4f84-9e5c-8b9d754e00a0
-- title:
--   Proposition 6(b), p. 38 — if E[|Δ^j h(V)|] < ∞, V ∼ Poisson(d_max), then h̆ is C^j on [0, d_max] with h̆^{(j)}(x) = E[Δ^j h(X)]
-- statement:
--   Let $h : \mathbb N \to \mathbb R$, $d_{\max} > 0$ and $V \sim \mathrm{Poisson}(d_{\max})$. If $\mathsf E[|\Delta^j h(V)|] < \infty$ for some $j \in \mathbb N$, then $\breve h(x) = \mathsf E[h(X)]$, $X \sim \mathrm{Poisson}(x)$, is of class $C^j$ on $[0, d_{\max}]$ and
--   $$\breve h^{(j)}(x) = \mathsf E[\Delta^j h(X)] \qquad \text{for all } x \in [0, d_{\max}].$$
--
--   Differentiating a Poisson mixture in its parameter amounts to taking forward differences of $h$; this gives the smoothness of the auxiliary costs $\breve c_e$ in Lemma 1.
--
--   **Formalization Note** Smoothness on the closed interval is `ContDiffOn` and the derivatives are `iteratedDerivWithin` relative to $[0, d_{\max}]$, so no value of $\breve h$ outside the interval is read. The condition $d_{\max} > 0$ gives the interval an interior; in the paper $d_{\max} > d_{\mathrm{tot}} \ge 0$.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 38, Appendix C, Proposition 6(b)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory

/-- Proposition 6(b), Appendix C, p. 38: if `E[|Δ^j h(V)|] < ∞` for `V ∼ Poisson(d_max)`, then
`h̆` is of class `C^j` on `[0, d_max]` and `h̆^{(j)}(x) = E[Δ^j h(X)]`, `X ∼ Poisson(x)`. -/
theorem proposition_6_b (h : ℕ → ℝ) (dmax : ℝ) (hd : 0 < dmax) (j : ℕ)
    (hint : Summable (fun k : ℕ => |deltaPow j h k| * poissonPmf dmax k)) :
    ContDiffOn ℝ j (poissonMean h) (Set.Icc 0 dmax) ∧
      ∀ x ∈ Set.Icc 0 dmax,
        iteratedDerivWithin j (poissonMean h) (Set.Icc 0 dmax) x =
          poissonMean (deltaPow j h) x := by sorry

end LargeCongestion.Poisson
