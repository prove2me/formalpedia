-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_proposition_5_i_sigma
-- name    : InvIntegration.Behavioral.proposition_5_i_sigma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:00.49062+00:00
-- url     : https://prove2.me/theorems/f19dc701-c81f-4300-be45-5c869637f66f
-- title:
--   Proposition 5 (i), p. 14 (PDF 14) — in σ: the integrated equilibrium ξI2 and v∗I are quasiconcave in σ > 0
-- statement:
--   Fix $\rho\in(-1,1)$. For $\sigma>0$ let $\xi_{I2}(\sigma)$ and $v^*_I(\sigma)$ be the equilibrium second-period fill rate and threshold valuation of the integrated market $N(2\mu,2(1+\rho)\sigma^2)$. Then
--   $$\sigma\mapsto\xi_{I2}(\sigma)\ \text{ and }\ \sigma\mapsto v^*_I(\sigma)\ \text{ are quasiconcave on } (0,\infty).$$
--
--   Quasiconcavity in $\sigma$ is the structural fact behind the variability threshold of Proposition 5 (iii).
--
--   **Formalization Note.** As in the paper, no condition on $\Pi(\mu,\sigma)$ is imposed here, and the proof's assumption $\mu+\hat z\sigma\ge 0$ is not added.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), p. 14 (PDF 14), Proposition 5 (i), in σ

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem proposition_5_i_sigma (P : Params) (hS : P.Standing) (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (xiI vI : ℝ → ℝ)
    (hE : ∀ σ : ℝ, 0 < σ → ∃ q : ℝ, IsEquilibrium P (2 * P.μ) (sdI σ ρ) q (vI σ) (xiI σ)) :
    QuasiconcaveOn ℝ (Set.Ioi (0 : ℝ)) xiI ∧ QuasiconcaveOn ℝ (Set.Ioi (0 : ℝ)) vI := by sorry

end InvIntegration.Behavioral
