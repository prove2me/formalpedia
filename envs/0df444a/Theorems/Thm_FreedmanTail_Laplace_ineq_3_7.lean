-- Prove2me | Theorems.Thm_FreedmanTail_Laplace_ineq_3_7
-- name    : FreedmanTail.Laplace.ineq_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:49.457979+00:00
-- url     : https://prove2.me/theorems/8604900c-570f-4218-814a-c576f6e15beb
-- title:
--   (3.7), p. 107 — E{exp(λX)} ≥ exp{f(λ) Var X} for X ≥ −1 and E(X) = 0
-- statement:
--   Let $X$ be a random variable with $X \ge -1$ (almost surely), $E(X) = 0$ and finite variance. With $f(\lambda) = e^{-\lambda} - 1 + \lambda$, for every $\lambda \ge 0$,
--   $$
--   E\{\exp(\lambda X)\} \ge \exp\{f(\lambda) \operatorname{Var} X\} ,
--   $$
--   where the left side may be $+\infty$.
--
--   This is the one-step inequality behind Proposition (3.6): applied conditionally to the increment $X_n$ given $\mathcal F_{n-1}$, it shows that $R_\lambda(T_n, S_n)$ has nondecreasing expectation.
--
--   **Formalization Note** Since $X$ is bounded only from below, $\exp(\lambda X)$ need not be integrable, so the expectation is the lower Lebesgue integral with values in $[0, \infty]$ (a Bochner integral would be $0$ for a non-integrable integrand and make the statement false). $X$ is assumed square-integrable, so that $\operatorname{Var} X$ is a finite real number; the page writes $\operatorname{Var} X$ without comment. The range $\lambda \ge 0$ is that of Proposition (3.6), which (3.7) serves.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 107 (PDF p. 8), (3.7)

import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (3.7), p. 107: `E{exp(λX)} ≥ exp{f(λ) Var X}` for random variables `X`
with `X ≥ −1` and `E(X) = 0`, for every `λ ≥ 0`. The expectation of `exp(λX)` (which need not
be integrable, `X` being bounded only below) is a lower Lebesgue integral in `[0, ∞]`; `X` is
assumed square-integrable so that `Var X` is finite. -/
theorem ineq_3_7 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_L2 : MemLp X 2 P)
    (hX_ge : ∀ᵐ ω ∂P, -1 ≤ X ω) (hX_mean : P[X] = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ENNReal.ofReal (Real.exp (f lam * variance X P)) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂P := by sorry

end FreedmanTail.Laplace
