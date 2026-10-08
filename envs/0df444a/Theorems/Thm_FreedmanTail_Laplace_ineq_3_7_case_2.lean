-- Prove2me | Theorems.Thm_FreedmanTail_Laplace_ineq_3_7_case_2
-- name    : FreedmanTail.Laplace.ineq_3_7_case_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:44.341983+00:00
-- url     : https://prove2.me/theorems/3dbc425e-e5a8-4ac2-b792-158fc692e3a8
-- title:
--   (3.7), Case 2, p. 107 — X ∈ {−b, a}, 0 < b ≤ 1, E X = 0 ⟹ E{exp(λX)} ≥ exp{f(λ) Var X}
-- statement:
--   Let $a > 0$ and $0 < b \le 1$, and let $X$ be a random variable that takes only the two values $-b$ and $a$ (almost surely) and has mean $E(X) = 0$. With $f(\lambda) = e^{-\lambda} - 1 + \lambda$, for every $\lambda \ge 0$,
--   $$
--   E\{\exp(\lambda X)\} \ge \exp\{f(\lambda) \operatorname{Var} X\} .
--   $$
--
--   Every mean-zero law on $[-1, \infty)$ is a mixture of such two-point laws, which is how the general inequality (3.7) is reached.
--
--   **Formalization Note** $X$ is assumed almost-everywhere measurable; the expectation is a Bochner integral, genuine because $\exp(\lambda X)$ is bounded.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 107 (PDF p. 8), proof of (3.7), Case 2

import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), proof of (3.7), Case 2, p. 107: if `X` takes only the two values `−b`
and `a`, with `a > 0` and `0 < b ≤ 1`, and has mean `0`, then
`E{exp(λX)} ≥ exp{f(λ) Var X}` for every `λ ≥ 0`. -/
theorem ineq_3_7_case_2 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_meas : AEMeasurable X P)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1)
    (hX_two : ∀ᵐ ω ∂P, X ω = -b ∨ X ω = a) (hX_mean : P[X] = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Real.exp (f lam * variance X P) ≤ ∫ ω, Real.exp (lam * X ω) ∂P := by sorry

end FreedmanTail.Laplace
