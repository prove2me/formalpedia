-- Prove2me | Theorems.Thm_GenEllipPot_Potential_lemma_2_1
-- name    : GenEllipPot.Potential.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:01.728996+00:00
-- url     : https://prove2.me/theorems/289c5b1d-6724-49c0-b1f7-4c25fddbaa99
-- title:
--   Lemma 2.1, p. 4: stochastic variance reduction
-- statement:
--   Under the filtered model of Section 2, let $\Gamma_t=\operatorname{Var}(\Theta^\star\mid\mathcal F_t)$. For every $t\ge1$, almost surely in the positive semidefinite matrix order,
--
--   $$\mathbb E[\Gamma_{t+1}\mid\mathcal F_t]\preceq\Gamma_t-\frac{\Gamma_t^\top A_tA_t^\top\Gamma_t}{\sigma^2+A_t^\top\Gamma_t A_t}.$$
--
--   This quantifies the expected reduction in posterior covariance after an observation. It is the paper's stochastic replacement for pathwise covariance monotonicity.
--
--   **Formalization Note.** Conditional expectation of a matrix is entrywise. At a zero denominator, the numerator also vanishes and the totalized inverse yields the limiting zero correction; no positive-noise assumption is added.
-- source:
--   Hamidi & Bayati, The Elliptical Potential Lemma for General Distributions with an Application to Linear Thompson Sampling, arXiv:2102.07987v3, p. 4, Lemma 2.1; proof pp. 7–8

import Mathlib
import Definitions.Def_GenEllipPot_Potential_Model

open MeasureTheory Matrix

namespace GenEllipPot.Potential

/-- Lemma 2.1, the stochastic variance reduction inequality, p. 4. -/
theorem lemma_2_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (M : Model Ω μ d) (t : ℕ) (ht : 1 ≤ t) :
    ∀ᵐ ω ∂μ,
      (postCov μ M.F M.Θ t ω -
        (M.σ ^ 2 + M.A t ω ⬝ᵥ (postCov μ M.F M.Θ t ω *ᵥ M.A t ω))⁻¹ •
          ((postCov μ M.F M.Θ t ω).transpose *
            Matrix.vecMulVec (M.A t ω) (M.A t ω) *
            postCov μ M.F M.Θ t ω) -
        meanPostCov μ M.F M.Θ t ω).PosSemidef := by sorry

end GenEllipPot.Potential
