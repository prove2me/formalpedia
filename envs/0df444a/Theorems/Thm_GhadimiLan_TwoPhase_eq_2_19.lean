-- Prove2me | Theorems.Thm_GhadimiLan_TwoPhase_eq_2_19
-- name    : GhadimiLan.TwoPhase.eq_2_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:39.343738+00:00
-- url     : https://prove2.me/theorems/ca5a57ce-db73-47bb-a7b7-e91f1fcea80f
-- title:
--   Equation (2.19) — one-run gradient tail
-- statement:
--   Under the same RSG run and constant-step oracle assumptions as Corollary 2.2, for every $\lambda>0$,
--
--   $$\Pr\{\|\nabla f(x_R)\|^2\ge\lambda L\mathcal B_N\}\le\frac1\lambda.$$
--
--   This is the one-run failure bound amplified by independent candidate runs.
--
--   **Formalization Note** The model includes the independent random output index and the integrability guards needed for the expectation behind this tail bound.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Eq. (2.19), p. 10

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Equation (2.19), p. 10: Markov's inequality for the one-run output. -/
theorem eq_2_19 {n N : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : Run P N μ) (hN : 1 ≤ N) :
    ∀ lam : ℝ, 0 < lam →
      μ {ω | lam * P.L * BN P.L (Df P) P.Dt P.σ N ≤
        ‖P.g (output A ω)‖ ^ 2} ≤ ENNReal.ofReal (1 / lam) := by sorry

end GhadimiLan.TwoPhase
