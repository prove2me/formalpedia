-- Prove2me | Theorems.Thm_FreedmanTail_Laplace_ineq_3_7_case_1
-- name    : FreedmanTail.Laplace.ineq_3_7_case_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:32.229543+00:00
-- url     : https://prove2.me/theorems/c44ad75e-be8e-4132-9322-d42a21760487
-- title:
--   (3.7), Case 1, p. 107 — X ∈ {−1, a}, E X = 0 ⟹ E{exp(λX)} ≥ exp{f(λ) Var X}
-- statement:
--   Let $a > 0$ and let $X$ be a random variable on a probability space that takes only the two values $-1$ and $a$ (almost surely) and has mean $E(X) = 0$. Then $P\{X = -1\} = a/(1+a)$, $P\{X = a\} = 1/(1+a)$ and $\operatorname{Var} X = E\{X^2\} = a$. With $f(\lambda) = e^{-\lambda} - 1 + \lambda$, for every $\lambda \ge 0$,
--   $$
--   E\{\exp(\lambda X)\} \ge \exp\{f(\lambda) \operatorname{Var} X\} .
--   $$
--
--   This is the two-point base case of inequality (3.7), the reverse (lower) counterpart of Bernstein's moment-generating-function bound.
--
--   **Formalization Note** $X$ is assumed almost-everywhere measurable and to take its two values almost surely; the conclusion is stated with the Bochner integral, which is genuine because $\exp(\lambda X)$ is bounded.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 107 (PDF p. 8), proof of (3.7), Case 1

import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), proof of (3.7), Case 1, p. 107: if `X` takes only the two values `−1`
and `a > 0` and has mean `0`, then `E{exp(λX)} ≥ exp{f(λ) Var X}` for every `λ ≥ 0`. -/
theorem ineq_3_7_case_1 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_meas : AEMeasurable X P)
    (a : ℝ) (ha : 0 < a) (hX_two : ∀ᵐ ω ∂P, X ω = -1 ∨ X ω = a) (hX_mean : P[X] = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Real.exp (f lam * variance X P) ≤ ∫ ω, Real.exp (lam * X ω) ∂P := by sorry

end FreedmanTail.Laplace
