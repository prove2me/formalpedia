-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_ineq_3_5
-- name    : FreedmanTail.Bernstein.ineq_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:50:19.30193+00:00
-- url     : https://prove2.me/theorems/b4ac0a2b-0d1a-4b29-8d8a-21aabef5ac22
-- title:
--   (3.5) — E exp(λX) ≤ 1 + e(λ) Var X ≤ exp[e(λ) Var X] for X ≤ 1, E X ≤ 0, λ ≥ 0
-- statement:
--   Let $X$ be a real random variable on a probability space with $X\le1$ almost surely and $E(X)\le0$, and let $\lambda\ge0$. With $e(\lambda)=e^{\lambda}-1-\lambda$,
--   $$E\{\exp(\lambda X)\}\le 1+e(\lambda)\operatorname{Var}X\le\exp[e(\lambda)\operatorname{Var}X].$$
--
--   The bound involves the variance, not the second moment $E(X^2)$; when $E(X)<0$ this is the sharper form. Applied conditionally to the increments of a supermartingale, it shows that $\exp\{\lambda S_n-e(\lambda)T_n\}$ is a supermartingale.
--
--   **Formalization Note** $X$ is assumed square integrable. The page states (3.5) for all $X$ with $X\le1$ and $E(X)\le0$ and adds "It is enough to prove (3.5) when $E(X^2)<\infty$": when $\operatorname{Var}X=\infty$ the right-hand sides are $+\infty$ and there is nothing to prove, so the restriction loses no content. Under it, $\exp(\lambda X)\le e^{\lambda}$ almost surely, so the expectation is a genuine finite integral.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 106 (PDF p. 7), display (3.5) in the proof of (3.3) Proposition

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), display (3.5), p. 106: for `λ ≥ 0` and a random variable `X` with
`X ≤ 1` and `E X ≤ 0`, `E exp(λX) ≤ 1 + e(λ) Var X ≤ exp[e(λ) Var X]`.
`X` is square integrable (the page reduces to that case: "It is enough to prove (3.5)
when E(X²) < ∞"). -/
theorem ineq_3_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX2 : MemLp X 2 P) (hX1 : X ≤ᵐ[P] 1) (hmean : ∫ ω, X ω ∂P ≤ 0) :
    ∫ ω, Real.exp (lam * X ω) ∂P ≤ 1 + e lam * variance X P ∧
      1 + e lam * variance X P ≤ Real.exp (e lam * variance X P) := by sorry

end FreedmanTail.Bernstein
