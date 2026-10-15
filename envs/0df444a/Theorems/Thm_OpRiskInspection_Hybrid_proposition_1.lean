-- Prove2me | Theorems.Thm_OpRiskInspection_Hybrid_proposition_1
-- name    : OpRiskInspection.Hybrid.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:22.162369+00:00
-- url     : https://prove2.me/theorems/64260056-b9eb-4529-ae72-eaf452ea7547
-- title:
--   Proposition 1, p. 14 — the optimal random strategy: effort inducement for $K>K_R$, error correction for $K<K_R$
-- statement:
--   There is a threshold $K_R$, depending only on the model parameters, such that for every inspection cost $K>0$:
--
--   1. (Effort inducement) If $K>K_R$ and $\alpha>0$ satisfies $\dfrac{e^\alpha}{(e^\alpha-1)^2}\alpha(\alpha+1)=\dfrac c{rK}$, then
--   $$
--   S^1_R=(v^1_R,P^1_R,w^1_R),\quad v^1_R=\frac r\alpha,\quad P^1_R=\frac Lr\alpha,\quad w^1_R=r\bar\pi+c\Big(1+\log\Big(\frac{L\lambda}{cr}\frac\alpha{1+\alpha}\Big)\Big)
--   $$
--   is an optimal random inspection strategy, attained with an optimal effort of the agent that is strictly positive at every $t\ge0$.
--   2. (Error correction) If $K<K_R$ and $v^0_R>0$ satisfies $\dfrac{(e^{r/v^0_R}-1)^2}{e^{r/v^0_R}(1+r/v^0_R)^2}=\dfrac{r^2K}{L\lambda}$, then $S^0_R=(v^0_R,0,r\bar\pi)$ is an optimal random inspection strategy, attained with an optimal effort that vanishes at every $t\ge0$.
--
--   It supplies the two candidate optima of the random policy in closed form.
--
--   **Formalization Note** $\alpha$ and $v^0_R$ have no closed form; they are variables carrying their defining equations and positivity, never chosen. The threshold is existential, as printed (the proof gives it by (EC.49)).
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 14, Proposition 1, (15), (16), (17)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting
import Definitions.Def_OpRiskInspection_Hybrid_Strategy

namespace OpRiskInspection.Hybrid

theorem proposition_1 (p : OpRiskInspection.RandomVsPeriodic.Params) (hp : OpRiskInspection.RandomVsPeriodic.Standing p) :
    ∃ KR : ℝ, ∀ K : ℝ, 0 < K →
      (KR < K → ∀ α : ℝ, 0 < α →
        Real.exp α / (Real.exp α - 1) ^ 2 * (α * (α + 1)) = p.c / (p.r * K) →
        ∃ a, OptimalStrategyWith p K OpRiskInspection.RandomVsPeriodic.randomLaw (p.r / α) (p.L / p.r * α)
            (p.r * p.pibar + p.c * (1 + Real.log (p.L * p.lam / (p.c * p.r) * (α / (1 + α))))) a ∧
          ∀ t, 0 ≤ t → 0 < a t) ∧
      (K < KR → ∀ v0 : ℝ, 0 < v0 →
        (Real.exp (p.r / v0) - 1) ^ 2 / (Real.exp (p.r / v0) * (1 + p.r / v0) ^ 2) =
          p.r ^ 2 * K / (p.L * p.lam) →
        ∃ a, OptimalStrategyWith p K OpRiskInspection.RandomVsPeriodic.randomLaw v0 0 (p.r * p.pibar) a ∧
          ∀ t, 0 ≤ t → a t = 0) := by sorry

end OpRiskInspection.Hybrid
