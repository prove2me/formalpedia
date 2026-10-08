-- Prove2me | Theorems.Thm_MatrixTail_Azuma_proposition3_1
-- name    : MatrixTail.Azuma.proposition3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:25:02.911986+00:00
-- url     : https://prove2.me/theorems/a343990f-6b24-4304-a80c-a04b08568a13
-- title:
--   Proposition 3.1 — the Laplace transform method: P{λmax(Y) ≥ t} ≤ e^{−θt}·E tr e^{θY} for every θ > 0
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $Y$ a random self-adjoint $d\times d$ complex matrix, $d\ge 1$. For every real $t$ and every $\theta>0$ at which $\mathbb E\operatorname{tr} e^{\theta Y}$ is finite,
--   $$
--   \mathbb P\{\lambda_{\max}(Y)\ge t\} \le e^{-\theta t}\cdot \mathbb E \operatorname{tr} e^{\theta Y}.
--   $$
--   Equivalently, $\mathbb P\{\lambda_{\max}(Y)\ge t\}\le \inf_{\theta>0}\{e^{-\theta t}\cdot\mathbb E\operatorname{tr} e^{\theta Y}\}$, which is how the paper states it.
--
--   This is the matrix analogue of the scalar Laplace transform (Chernoff) bound: a tail bound for the largest eigenvalue follows from a bound on the trace of the matrix moment generating function. The matrix Azuma inequality is derived by combining it with such a bound for a martingale sum.
--
--   **Formalization Note** The infimum over $\theta>0$ is stated as the bound for every $\theta>0$ at which $\omega\mapsto\operatorname{tr}e^{\theta Y(\omega)}$ is integrable; values of $\theta$ where the expectation is infinite give a trivial bound in the paper's convention, so the two readings agree. $Y$ is measurable and Hermitian at every outcome.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 9, Proposition 3.1

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- **Proposition 3.1 (The Laplace Transform Method).** Tropp, *User-Friendly Tail Bounds for Sums of Random
Matrices*, arXiv:1004.4389v7, p. 9: "Let `Y` be a random self-adjoint matrix. For all `t ∈ ℝ`,
`P {λmax(Y) ≥ t} ≤ inf_{θ>0} { e^{−θt} · E tr e^{θY} }`." Restated locally (also a milestone of mission I);
the proof of Theorem 7.1 starts from it, display (7.4), p. 29.

**Formalization Note.**
* Matrices are complex `d × d` with `d ≥ 1` (`[NeZero d]`); for `d = 0`, `λmax = sSup ∅ = 0` and the trace
  is `0`, and the bound would fail at `t ≤ 0`.
* `Y` is measurable and Hermitian at every outcome; `P` is a probability measure.
* The infimum over `θ > 0` is stated as the bound for every `θ > 0` at which `E tr e^{θY}` exists, i.e. at
  which `ω ↦ tr e^{θY(ω)}` is integrable (the §2.2 regularity made explicit). The paper admits non-existent
  expectations, whose value is then `+∞`; `P ≤ inf_θ F(θ)` is equivalent to `P ≤ F(θ)` for every `θ`, so this
  reading is exact. Without the integrability hypothesis Lean's integral would be `0`.
* `e^{θY}` is `cfc Real.exp (θ • Y)` and `tr e^{θY}` is the real part of its trace (`trExp`). -/
theorem proposition3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] (Y : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hY_meas : Measurable Y) (hY_herm : ∀ ω, (Y ω).IsHermitian)
    (t θ : ℝ) (hθ : 0 < θ) (hint : Integrable (fun ω => trExp (θ • Y ω)) P) :
    P.real {ω | t ≤ lambdaMax (Y ω)} ≤ Real.exp (-θ * t) * ∫ ω, trExp (θ • Y ω) ∂P := by sorry

end MatrixTail.Azuma
