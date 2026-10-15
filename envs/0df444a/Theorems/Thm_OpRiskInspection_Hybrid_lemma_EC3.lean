-- Prove2me | Theorems.Thm_OpRiskInspection_Hybrid_lemma_EC3
-- name    : OpRiskInspection.Hybrid.lemma_EC3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:13.135182+00:00
-- url     : https://prove2.me/theorems/c61c1c5d-5c18-4f32-933b-1a7b4de5e08b
-- title:
--   Lemma EC.3, p. ec8 — the optimal random strategy is $S^1_R$ or $S^0_R$
-- statement:
--   Fix $K>0$. Let $\alpha>0$ satisfy $\dfrac{e^\alpha}{(e^\alpha-1)^2}\,\alpha(\alpha+1)=\dfrac{c}{rK}$, and let $v^0_R>0$ satisfy (16):
--   $$
--   \frac{(e^{r/v^0_R}-1)^2}{e^{r/v^0_R}(1+r/v^0_R)^2}=\frac{r^2K}{L\lambda}.
--   $$
--   Put
--   $$
--   S^1_R=\Big(\frac r\alpha,\ \frac Lr\alpha,\ r\bar\pi+c\Big(1+\log\Big(\frac{L\lambda}{cr}\frac{\alpha}{1+\alpha}\Big)\Big)\Big),\qquad S^0_R=(v^0_R,\ 0,\ r\bar\pi),
--   $$
--   the strategies (15) and (17). Then the optimal random inspection strategy is one of them: either $S^1_R$ or $S^0_R$ is an optimal inspection strategy under the random policy (feasible, attained with an optimal effort of the agent and participation, and at least every achievable random payoff).
--
--   This reduces the optimization over the random policy to two candidates.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. ec8, Lemma EC.3; strategies (15), (17), p. 14

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting
import Definitions.Def_OpRiskInspection_Hybrid_Strategy

namespace OpRiskInspection.Hybrid

theorem lemma_EC3 (p : OpRiskInspection.RandomVsPeriodic.Params) (hp : OpRiskInspection.RandomVsPeriodic.Standing p) (K : ℝ) (hK : 0 < K)
    (α : ℝ) (hα : 0 < α)
    (hαdef : Real.exp α / (Real.exp α - 1) ^ 2 * (α * (α + 1)) = p.c / (p.r * K))
    (v0 : ℝ) (hv0 : 0 < v0)
    (hv0def : (Real.exp (p.r / v0) - 1) ^ 2 / (Real.exp (p.r / v0) * (1 + p.r / v0) ^ 2) =
      p.r ^ 2 * K / (p.L * p.lam)) :
    (∃ a, OptimalStrategyWith p K OpRiskInspection.RandomVsPeriodic.randomLaw (p.r / α) (p.L / p.r * α)
        (p.r * p.pibar + p.c * (1 + Real.log (p.L * p.lam / (p.c * p.r) * (α / (1 + α))))) a) ∨
    (∃ a, OptimalStrategyWith p K OpRiskInspection.RandomVsPeriodic.randomLaw v0 0 (p.r * p.pibar) a) := by sorry

end OpRiskInspection.Hybrid
