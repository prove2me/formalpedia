-- Prove2me | Theorems.Thm_NonmonotoneSubmod_QueryLB_chernoff_theorem_1_2
-- name    : NonmonotoneSubmod.QueryLB.chernoff_theorem_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:14:16.720571+00:00
-- url     : https://prove2.me/theorems/612bcea6-ee44-4921-8508-71a6336a5dd6
-- title:
--   Theorem 1.2 — Chernoff bound for independent variables in $[-1,1]$
-- statement:
--   Let $Y_1, \dots, Y_t$ be independent real random variables on a probability space, each taking values in $[-1, 1]$ and with $\mathbb{E}[Y_i] = 0$. Then for every $\lambda > 0$,
--
--   $$
--   \Pr\Bigl[\sum_{i=1}^t Y_i > \lambda\Bigr] \le e^{-\lambda^2/2t}.
--   $$
--
--   The paper quotes this bound from Alon and Spencer and uses it for all its concentration arguments, including the bound on unbalanced queries in the proof of Theorem 4.5.
--
--   **Formalization Note** Random variables are measurable maps `Y i : Ω → ℝ`, mutually independent (`iIndepFun`) under a probability measure, with values in $[-1,1]$ at every point; the mean is the Bochner integral, which is the true mean since each $Y_i$ is bounded and measurable. The hypothesis $\lambda > 0$ is Alon–Spencer's and is needed: for $\lambda < 0$ and $Y_i \equiv 0$ the left side is $1$. For $t = 0$ the exponent reads $-\lambda^2/0 = 0$ in Lean, and the bound $1$ is correct.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Theorem 1.2 (quoted from Alon–Spencer, The Probabilistic Method)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace NonmonotoneSubmod.QueryLB

/-- Theorem 1.2 (Feige–Mirrokni–Vondrák 2011, p. 1137, quoted from Alon–Spencer): if
`Y₁, …, Y_t` are independent random variables with values in `[−1, 1]` and `E[Yᵢ] = 0`, then
`Pr[∑ Yᵢ > λ] ≤ e^{−λ²/2t}` for every `λ > 0`. -/
theorem chernoff_theorem_1_2 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℕ) (Y : Fin t → Ω → ℝ) (hmeas : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hbd : ∀ i ω, Y i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0) (lam : ℝ) (hlam : 0 < lam) :
    μ.real {ω | lam < ∑ i, Y i ω} ≤ Real.exp (-(lam ^ 2 / (2 * t))) := by sorry

end NonmonotoneSubmod.QueryLB
