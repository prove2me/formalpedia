-- Prove2me | Theorems.Thm_GhadimiLan_TwoPhase_theorem_2_4_a
-- name    : GhadimiLan.TwoPhase.theorem_2_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:55.791076+00:00
-- url     : https://prove2.me/theorems/18990b88-303a-4d8f-9485-c90558fdedc6
-- title:
--   Theorem 2.4(a) — two-phase gradient tail at arbitrary parameters
-- statement:
--   Run the two-phase RSG method with $S,N,T\ge1$: draw $S$ independent constant-step RSG candidates, estimate each gradient from $T$ further oracle calls, and select a candidate with minimum estimated-gradient norm. With $\mathcal B_N$ from (2.14), every $\lambda>0$ satisfies
--
--   $$\Pr\left\{\|\nabla f(\bar x^*)\|^2\ge2\left(4L\mathcal B_N+\frac{3\lambda\sigma^2}{T}\right)\right\}\le\frac{S+1}{\lambda}+2^{-S}.$$
--
--   This is the parameter-free tail estimate used to select the run count, iteration limit, and sample size in part (b).
--
--   **Formalization Note** The selection may be any minimizer (any tie rule, no measurability assumed). The paper's intermediate (2.31) is not assumed; the final bound also follows by controlling its error with the maximum error term in (2.28).
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Theorem 2.4(a), Eq. (2.23), p. 12

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Theorem 2.4(a), Eq. (2.23), p. 12. -/
theorem theorem_2_4_a {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : System (S := S) (N := N) (T := T) P μ)
    (hS : 1 ≤ S) (hN : 1 ≤ N) (hT : 1 ≤ T) :
    ∀ lam : ℝ, 0 < lam →
      μ {ω | 2 * (4 * P.L * BN P.L (Df P) P.Dt P.σ N +
        3 * lam * P.σ ^ 2 / T) ≤ ‖P.g (chosen A ω)‖ ^ 2} ≤
          ENNReal.ofReal (((S : ℝ) + 1) / lam + (1 / 2 : ℝ) ^ S) := by sorry

end GhadimiLan.TwoPhase
