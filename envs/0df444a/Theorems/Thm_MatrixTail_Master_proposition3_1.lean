-- Prove2me | Theorems.Thm_MatrixTail_Master_proposition3_1
-- name    : MatrixTail.Master.proposition3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:15:07.661813+00:00
-- url     : https://prove2.me/theorems/a7789d6e-81fa-468c-89e3-0c74e22c2c91
-- title:
--   Proposition 3.1 — the Laplace transform method: P{λmax(Y) ≥ t} ≤ e^{−θt}·E tr e^{θY}
-- statement:
--   Let $Y$ be a random $d\times d$ complex Hermitian matrix on a probability space, with $d\ge 1$. For every $t\in\mathbb R$ and every $\theta>0$ at which $\mathbb E \operatorname{tr} e^{\theta Y}$ exists,
--   $$\mathbb P\{\lambda_{\max}(Y)\ge t\} \le e^{-\theta t}\cdot \mathbb E\operatorname{tr} e^{\theta Y}.$$
--   Equivalently, $\mathbb P\{\lambda_{\max}(Y)\ge t\}\le \inf_{\theta>0}\{e^{-\theta t}\,\mathbb E\operatorname{tr}e^{\theta Y}\}$, the form in which the paper states it.
--
--   This is the matrix analogue of the scalar Laplace transform (Chernoff) bound: a tail bound for the largest eigenvalue reduces to a bound on the trace of the matrix moment generating function.
--
--   **Formalization Note.** The infimum is stated as the bound for each $\theta>0$ at which $\omega\mapsto\operatorname{tr}e^{\theta Y(\omega)}$ is integrable; the paper admits expectations that do not exist (value $+\infty$), so this reading is exact. The dimension is assumed positive: for $d=0$ the largest eigenvalue would be $0$ and the trace $0$.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 9, Proposition 3.1

import Mathlib
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Master

/-- **Proposition 3.1 (The Laplace Transform Method).** Tropp, *User-Friendly Tail Bounds for Sums of Random
Matrices*, arXiv:1004.4389v7, p. 9: "Let `Y` be a random self-adjoint matrix. For all `t ∈ ℝ`,
`P {λmax(Y) ≥ t} ≤ inf_{θ>0} { e^{−θt} · E tr e^{θY} }`."

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

end MatrixTail.Master
