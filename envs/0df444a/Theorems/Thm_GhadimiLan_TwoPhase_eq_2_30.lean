-- Prove2me | Theorems.Thm_GhadimiLan_TwoPhase_eq_2_30
-- name    : GhadimiLan.TwoPhase.eq_2_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:05:00.086442+00:00
-- url     : https://prove2.me/theorems/f1a97a67-91a5-408c-8c94-858a42ca8a2f
-- title:
--   Equation (2.30) — post-optimization estimation-error tail
-- statement:
--   For each of $S$ RSG candidates $\bar x_s$, average $T\ge1$ subsequent oracle gradients to obtain $\widehat g_s$. The oracle is conditionally unbiased at each candidate and its error has mean squared norm at most $\sigma^2$. For every $\lambda>0$, each candidate has error probability at most $1/\lambda$, and
--
--   $$\Pr\left\{\max_{1\le s\le S}\|\widehat g_s-\nabla f(\bar x_s)\|^2\ge\frac{\lambda\sigma^2}{T}\right\}\le\frac S\lambda.$$
--
--   This bounds the sampling error across all candidates without requiring their post-optimization samples to be independent of each other.
--
--   **Formalization Note** Each candidate is measurable at time zero of its post-optimization filtration; the oracle's conditional mean is taken relative to that information.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Eq. (2.30) and preceding display, p. 13

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Equation (2.30), p. 13, including the preceding per-candidate bound. -/
theorem eq_2_30 {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : System (S := S) (N := N) (T := T) P μ)
    (hT : 1 ≤ T) :
    (∀ s : Fin S, ∀ lam : ℝ, 0 < lam →
      μ {ω | lam * P.σ ^ 2 / T ≤
        ‖estimate A.runs A.η T s ω - P.g (output (A.runs s) ω)‖ ^ 2} ≤
          ENNReal.ofReal (1 / lam)) ∧
    (∀ lam : ℝ, 0 < lam →
      μ {ω | ∃ s : Fin S, lam * P.σ ^ 2 / T ≤
        ‖estimate A.runs A.η T s ω - P.g (output (A.runs s) ω)‖ ^ 2} ≤
          ENNReal.ofReal ((S : ℝ) / lam)) := by sorry

end GhadimiLan.TwoPhase
