-- Prove2me | Theorems.Thm_GenEllipPot_Potential_quadratic_bound
-- name    : GenEllipPot.Potential.quadratic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:52.637487+00:00
-- url     : https://prove2.me/theorems/df5d2219-7f9a-4d43-a56d-138a00d92395
-- title:
--   Proof of Theorem 2.1, p. 10: AₜᵀΓₜAₜ ≤ 1
-- statement:
--   Under the filtered model of Section 2, for every time $t\ge1$, the action $A_t$ and posterior covariance $\Gamma_t$ satisfy, almost surely,
--
--   $$A_t^\top\Gamma_t A_t\le1.$$
--
--   The unit bound supplies the domain of the scalar logarithm inequality used in the proof of Theorem 2.1.
--
--   **Formalization Note.** The unit bounds on $A_t$ and $\Theta^\star$ are Euclidean bounds; $\Gamma_t$ is conditional covariance, not a deterministic Gram matrix.
-- source:
--   Hamidi & Bayati, The Elliptical Potential Lemma for General Distributions with an Application to Linear Thompson Sampling, arXiv:2102.07987v3, p. 10, proof of Theorem 2.1

import Mathlib
import Definitions.Def_GenEllipPot_Potential_Model

open MeasureTheory Matrix

namespace GenEllipPot.Potential

/-- The quadratic form bound stated in the proof of Theorem 2.1, p. 10. -/
theorem quadratic_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (M : Model Ω μ d) (t : ℕ) (ht : 1 ≤ t) :
    ∀ᵐ ω ∂μ, M.A t ω ⬝ᵥ (postCov μ M.F M.Θ t ω *ᵥ M.A t ω) ≤ 1 := by sorry

end GenEllipPot.Potential
