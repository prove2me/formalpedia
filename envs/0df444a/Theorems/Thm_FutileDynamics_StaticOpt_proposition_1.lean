-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_proposition_1
-- name    : FutileDynamics.StaticOpt.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:26.072663+00:00
-- url     : https://prove2.me/theorems/1b1d2e27-329b-4d1b-a5f7-0bd4fb69283a
-- title:
--   Proposition 1, p. 14 — OPT(δθ, T) = T · OPT(δθ, 1) for every point mass
-- statement:
--   For every shock $\theta\in\Theta$, the known-distribution benchmark at the point mass $\delta_\theta$ is linear in the horizon:
--   $$\mathrm{OPT}(\delta_\theta,T)=T\cdot\mathrm{OPT}(\delta_\theta,1).$$
--
--   With a point-mass distribution the agent holds no private information. The lower bound (Lemma 2) and the upper bound (Lemma 3) both pass through this identity.
--
--   **Formalization Note** $\mathrm{OPT}$ is the real supremum of the principal utility over all incentive compatible dynamic mechanisms, with arbitrary report spaces. Assumed: $0<T$, $\Theta$ standard Borel and nonempty, and the model conventions.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), p. 14, Proposition 1

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Proposition 1** (p. 14): for any `θ ∈ Θ`, `OPT(δ_θ, T) = T · OPT(δ_θ, 1)`. -/
theorem proposition_1 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) :
    ∀ θ : Θ, OPT G (Measure.dirac θ) T = T * OPT G (Measure.dirac θ) 1 := by sorry

end FutileDynamics.StaticOpt
