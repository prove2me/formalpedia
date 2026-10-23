-- Prove2me | Theorems.Thm_GameRandEnv_FirstOrder_sufficient_entropy_bound
-- name    : GameRandEnv.FirstOrder.sufficient_entropy_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:42.999848+00:00
-- url     : https://prove2.me/theorems/eceeefc3-6db6-4e1c-a93c-75b2b059e35d
-- title:
--   §5.1 sufficient condition, p. 11 — under (3.1), H(π̄) − H(π̄∗) ≥ ∫ ln π∗(x|y) d(π̄ − π̄∗)
-- statement:
--   In the setting of §2.1, let $F:\Pi\to\mathbb R$ satisfy Assumption 2.1, let $\eta>0$, and let $\bar\pi^*\in\Pi$ satisfy the first-order equation (3.1), with density $\pi^*(x|y)$ with respect to $\mathrm{Leb}\times\mathsf m$. Let $\bar\pi\in\Pi$ be absolutely continuous with respect to $\mathrm{Leb}\times\mathsf m$. Then $\ln\pi^*(x|y)$ is integrable with respect to both $\bar\pi$ and $\bar\pi^*$, and
--   $$H(\bar\pi)-H(\bar\pi^*)\ge\int\ln\pi^*(x|y)\,(\bar\pi-\bar\pi^*)(d\bar x),$$
--   where $H$ is relative entropy with respect to $\mathrm{Leb}\times\mathsf m$ (the left-hand side may be $+\infty$).
--
--   This is the entropy half of the sufficiency direction of Theorem 3.1; combined with the convexity bound for $F$ and (3.1) it gives $V(\bar\pi)\ge V(\bar\pi^*)$.
--
--   **Formalization Note** The integrability of $\ln\pi^*$ is stated as part of the conclusion so that the right-hand side is a genuine integral (it follows from (3.1), Assumption 2.1 and $\bar\pi,\bar\pi^*\in\Pi$). $H$ takes values in $(-\infty,+\infty]$ and the inequality is read in the extended reals.
-- source:
--   Conforti, Kazeykina, Ren, Game on random environment, mean-field Langevin system and neural networks, arXiv:2004.02457v2, p. 11, §5.1, proof of Theorem 3.1, Sufficient condition

import Mathlib
import Definitions.Def_GameRandEnv_FirstOrder_Setting

open MeasureTheory Filter Topology

namespace GameRandEnv.FirstOrder

theorem sufficient_entropy_bound {d : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [IsProbabilityMeasure m] (p : ℝ)
    (F : Measure (Rd d × Y) → ℝ) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ)
    (hA : Assumption21 m p F δF) (η : ℝ) (hη : 0 < η)
    (πs π : Measure (Rd d × Y)) (hπs : πs ∈ Pi m p) (hfoc : FirstOrderCondition m δF η πs)
    (hπ : π ∈ Pi m p) (hac : π ≪ volume.prod m) :
    Integrable (logDens m πs) π ∧ Integrable (logDens m πs) πs ∧
      ((∫ z, logDens m πs z ∂π - ∫ z, logDens m πs z ∂πs : ℝ) : EReal) ≤
        relEnt m π - relEnt m πs := by sorry

end GameRandEnv.FirstOrder
