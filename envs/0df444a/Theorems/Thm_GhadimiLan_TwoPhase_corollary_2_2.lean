-- Prove2me | Theorems.Thm_GhadimiLan_TwoPhase_corollary_2_2
-- name    : GhadimiLan.TwoPhase.corollary_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:51.508069+00:00
-- url     : https://prove2.me/theorems/8dc85fe8-f321-471c-94bb-648889e50d39
-- title:
--   Corollary 2.2 — one-run constant-step gradient bound
-- statement:
--   Consider one RSG run on a smooth, lower-bounded objective, with a conditionally unbiased stochastic gradient oracle whose mean squared error is at most $\sigma^2$. Use the constant stepsizes (2.13) and draw the output index $R$ according to (2.3). For $N\ge1$,
--
--   $$\frac1L\mathbb E\|\nabla f(x_R)\|^2\le\mathcal B_N:=\frac{LD_f^2}{N}+\left(\widetilde D+\frac{D_f^2}{\widetilde D}\right)\frac{\sigma}{\sqrt N},\qquad D_f=\sqrt{\frac{2(f(x_1)-f^*)}{L}}.$$
--
--   This supplies the mean bound used in the two-phase analysis.
--
--   **Formalization Note** The expectation's integrand is explicitly integrable. The random index is independent of the run's noise; $L,\sigma,\widetilde D>0$ make the stepsize well-defined and positive.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Corollary 2.2, Eqs. (2.13)–(2.14), p. 8

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Corollary 2.2, Eq. (2.14), p. 8, with (2.13) and (2.3). -/
theorem corollary_2_2 {n N : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : Run P N μ) (hN : 1 ≤ N) :
    Integrable (fun ω => ‖P.g (output A ω)‖ ^ 2) μ ∧
    (1 / P.L) * ∫ ω, ‖P.g (output A ω)‖ ^ 2 ∂μ ≤
      BN P.L (Df P) P.Dt P.σ N := by sorry

end GhadimiLan.TwoPhase
