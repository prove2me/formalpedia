-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_proposition_5_a
-- name    : LargeCongestion.Poisson.proposition_5_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:32.779048+00:00
-- url     : https://prove2.me/theorems/691118d2-c91a-4b13-aa75-984123488627
-- title:
--   Proposition 5(a), p. 37 — E[|h(Y)|] ≤ e^{x−y} E[|h(X)|] for Y ∼ Poisson(y), X ∼ Poisson(x), y ≤ x
-- statement:
--   Let $h : \mathbb N \to \mathbb R$, $0 \le y \le x$, $X \sim \mathrm{Poisson}(x)$ and $Y \sim \mathrm{Poisson}(y)$. Then
--   $$\mathsf E[|h(Y)|] \le e^{x-y}\,\mathsf E[|h(X)|],$$
--   where both sides may be $+\infty$.
--
--   Integrability under a Poisson law therefore passes to every smaller parameter; this is how condition (18), stated at $d_{\max}$, controls expectations at every load in $[0, d_{\max}]$.
--
--   **Formalization Note** Both expectations are computed in $[0,\infty]$, so the inequality is meaningful when the right side is infinite.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 37, Appendix C, Proposition 5(a)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Proposition 5(a), Appendix C, p. 37: for `X ∼ Poisson(x)` and `Y ∼ Poisson(y)` with
`0 ≤ y ≤ x`, `E[|h(Y)|] ≤ e^{x−y} E[|h(X)|]`, both sides in `[0, ∞]`. -/
theorem proposition_5_a (h : ℕ → ℝ) (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) :
    ∑' k : ℕ, ENNReal.ofReal (|h k| * poissonPmf y k) ≤
      ENNReal.ofReal (Real.exp (x - y)) * ∑' k : ℕ, ENNReal.ofReal (|h k| * poissonPmf x k) := by sorry

end LargeCongestion.Poisson
