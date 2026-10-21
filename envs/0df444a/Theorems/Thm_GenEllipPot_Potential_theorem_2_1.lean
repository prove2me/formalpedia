-- Prove2me | Theorems.Thm_GenEllipPot_Potential_theorem_2_1
-- name    : GenEllipPot.Potential.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:55.607461+00:00
-- url     : https://prove2.me/theorems/a0183372-1c21-450d-8899-22913cb2b445
-- title:
--   Theorem 2.1, p. 4: general elliptical potential bound
-- statement:
--   In the filtered model of Section 2, let $\Gamma_t=\operatorname{Var}(\Theta^\star\mid\mathcal F_t)$ and let $T\ge0$ be an integer horizon. Conditional on the initial information $\mathcal F_1$, almost surely,
--
--   $$\mathbb E\!\left[\sum_{t=1}^T A_t^\top\Gamma_t A_t\,\middle|\,\mathcal F_1\right]\le 2\max(\sigma^2,1)\log\det(I+T\Gamma_1).$$
--
--   The bound controls the expected sum of adaptive posterior quadratic forms for general prior and noise distributions. It is the paper's main extension of the classical deterministic elliptical potential lemma.
--
--   **Formalization Note.** The paper prints an unconditional expectation against a right side containing random $\Gamma_1$. The conditional statement is the coherent general reading when $\mathcal F_1$ is not trivial; it reduces to the printed display when $\mathcal F_1$ is trivial. The model explicitly requires each $Y_t$ to be square-integrable.
-- source:
--   Hamidi & Bayati, The Elliptical Potential Lemma for General Distributions with an Application to Linear Thompson Sampling, arXiv:2102.07987v3, p. 4, Theorem 2.1; proof p. 10

import Mathlib
import Definitions.Def_GenEllipPot_Potential_Model

open MeasureTheory Matrix
open scoped MeasureTheory

namespace GenEllipPot.Potential

/-- Conditional version of Theorem 2.1, p. 4. The paper's random `Γ₁` makes
conditioning on the initial information necessary. -/
theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (M : Model Ω μ d) (T : ℕ) :
    ∀ᵐ ω ∂μ,
      μ[rewardSum μ M.F M.Θ M.A T | M.F 1] ω ≤
      2 * max (M.σ ^ 2) 1 * potF (postCov μ M.F M.Θ 1 ω) (T : ℝ) := by sorry

end GenEllipPot.Potential
