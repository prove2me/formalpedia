-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_proposition_5_i_rho
-- name    : InvIntegration.Behavioral.proposition_5_i_rho
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:10.216978+00:00
-- url     : https://prove2.me/theorems/f0667699-bf34-4ca2-a957-9642a2f25308
-- title:
--   Proposition 5 (i), p. 14 (PDF 14) — in ρ: the integrated equilibrium ξI2 and v∗I are quasiconcave in ρ ∈ (−1, 1)
-- statement:
--   Fix $\sigma>0$. For $\rho\in(-1,1)$ let $\xi_{I2}(\rho)$ and $v^*_I(\rho)$ be the equilibrium second-period fill rate and threshold valuation of the integrated market $N(2\mu,2(1+\rho)\sigma^2)$. Then
--   $$\rho\mapsto\xi_{I2}(\rho)\ \text{ and }\ \rho\mapsto v^*_I(\rho)\ \text{ are quasiconcave on } (-1,1).$$
--
--   Quasiconcavity of $v^*_I$ in $\rho$ is the structural fact behind the correlation threshold of Proposition 5 (ii).
--
--   **Formalization Note.** $\xi_{I2}$ and $v^*_I$ are given as functions that are equilibrium values at every $\rho\in(-1,1)$; by Proposition 3 they are the equilibrium values.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), p. 14 (PDF 14), Proposition 5 (i), in ρ

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem proposition_5_i_rho (P : Params) (hS : P.Standing) (σ : ℝ) (hσ : 0 < σ)
    (xiI vI : ℝ → ℝ)
    (hE : ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1, ∃ q : ℝ, IsEquilibrium P (2 * P.μ) (sdI σ ρ) q (vI ρ) (xiI ρ)) :
    QuasiconcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) xiI ∧ QuasiconcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) vI := by sorry

end InvIntegration.Behavioral
