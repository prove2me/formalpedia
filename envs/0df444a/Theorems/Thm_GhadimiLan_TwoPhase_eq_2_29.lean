-- Prove2me | Theorems.Thm_GhadimiLan_TwoPhase_eq_2_29
-- name    : GhadimiLan.TwoPhase.eq_2_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:31.109985+00:00
-- url     : https://prove2.me/theorems/26baf040-ffcd-42da-8cdc-eca81ac15c43
-- title:
--   Equation (2.29) — independent-run probability amplification
-- statement:
--   Run the constant-step RSG method independently $S\ge1$ times, obtaining candidates $\bar x_s$. For $N\ge1$, the probability that every candidate's squared gradient is at least $2L\mathcal B_N$ factors as
--
--   $$\Pr\left\{\min_{1\le s\le S}\|\nabla f(\bar x_s)\|^2\ge2L\mathcal B_N\right\}=\prod_{s=1}^{S}\Pr\left\{\|\nabla f(\bar x_s)\|^2\ge2L\mathcal B_N\right\}\le2^{-S}.$$
--
--   This is the probability amplification supplied by independent optimization runs.
--
--   **Formalization Note** Independence is asserted directly for the candidate outputs. Each candidate is an RSG output with its own oracle run; the one-run tail bound is not assumed as a field of the model.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Eq. (2.29), p. 12

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Equation (2.29), p. 12: the S independent RSG runs amplify the one-run tail. -/
theorem eq_2_29 {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n Ξ) (A : System (S := S) (N := N) (T := T) P μ)
    (hS : 1 ≤ S) (hN : 1 ≤ N) :
    μ {ω | ∀ s : Fin S,
      2 * P.L * BN P.L (Df P) P.Dt P.σ N ≤
        ‖P.g (output (A.runs s) ω)‖ ^ 2} =
      ∏ s : Fin S, μ {ω |
        2 * P.L * BN P.L (Df P) P.Dt P.σ N ≤
          ‖P.g (output (A.runs s) ω)‖ ^ 2} ∧
    μ {ω | ∀ s : Fin S,
      2 * P.L * BN P.L (Df P) P.Dt P.σ N ≤
        ‖P.g (output (A.runs s) ω)‖ ^ 2} ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ S) := by sorry

end GhadimiLan.TwoPhase
