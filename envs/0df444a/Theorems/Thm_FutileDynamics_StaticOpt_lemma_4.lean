-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_lemma_4
-- name    : FutileDynamics.StaticOpt.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:35.689347+00:00
-- url     : https://prove2.me/theorems/f7f95ca2-4e7d-4f5f-bc67-feaf80b1c135
-- title:
--   Lemma 4, p. ec 5 — every IC dynamic mechanism A induces S(A) ∈ S×1 with PrincipalUtility(A, σ, δθ, T) = T·PrincipalUtility(S(A), σTR, δθ, 1)
-- statement:
--   Let $A$ be an incentive compatible dynamic mechanism with recommended strategy $\sigma$. Then there is a single-round direct IC/IR mechanism $S(A)\in\mathcal S^{\times1}$ such that, for every $\theta\in\Theta$,
--   $$\mathrm{PrincipalUtility}(A,\sigma,\delta_\theta,T)=T\cdot\mathrm{PrincipalUtility}(S(A),\sigma^{TR},\delta_\theta,1).$$
--   Here $\sigma^{TR}$ is the truthful strategy: participate (CONTINUE), then report the shock.
--
--   This is a revelation-principle-type reduction. Restricted to point masses, any IC dynamic mechanism is no better per round than a single-round direct IC mechanism.
--
--   **Formalization Note** $S(A)$ is asserted to exist, given by a jointly measurable direct rule $\tilde\pi$ with $\tilde\pi(\mathrm{PASS},\cdot)=\emptyset$ that is IC at horizon 1 for every distribution. Assumed: $0<T$, $\Theta$ standard Borel and nonempty, and the model conventions. The recommended strategy of $A$ is jointly measurable in $F$, which makes $\theta\mapsto S(A)_\theta$ measurable.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), p. ec 5, Lemma 4

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Lemma 4** (p. ec 5): for any incentive compatible dynamic mechanism `A` with recommended strategy
`σ` there is a single-round direct IC/IR mechanism `S(A) ∈ S^{×1}` (rule `d`) such that for every `θ`,
`PrincipalUtility(A, σ, δ_θ, T) = T · PrincipalUtility(S(A), σ^TR, δ_θ, 1)`. -/
theorem lemma_4 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) :
    ∀ A : DynMech Θ Ω, IsIC G A T → ∃ d : DirectRule G, SingleRoundIC G d ∧
      ∀ θ : Θ, principalUtility G A A.recom (Measure.dirac θ) T =
        T * principalUtility G (repeatDirect G d) (repeatDirect G d).recom (Measure.dirac θ) 1 := by sorry

end FutileDynamics.StaticOpt
