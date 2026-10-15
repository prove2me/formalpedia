-- Prove2me | Theorems.Thm_OpRiskInspection_Hybrid_binding_participation
-- name    : OpRiskInspection.Hybrid.binding_participation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:24.98385+00:00
-- url     : https://prove2.me/theorems/a5c18508-a986-45a7-a05c-0e23b5dc8ea0
-- title:
--   §3.2, p. 10, (6) — the participation constraint binds at an optimal strategy and $\Pi_I=V_I$
-- statement:
--   Consider any inspection policy whose interval laws $F_v$ ($v>0$) are probability measures giving no mass to $(-\infty,0]$; the random, periodic and hybrid policies are of this kind. Let $K>0$, and let $(v,P,w)$ with $v>0$, $P\ge0$, $w\ge0$ and an optimal effort $a$ of the agent be a strategy at which the agent participates, $\pi(a;v,P,w)\ge\bar\pi$, and whose payoff $\Pi(v,P,w)$ is at least every achievable payoff of the policy. Then the participation constraint (5) binds and the principal's payoff equals the reduced payoff (6):
--   $$
--   \pi(a;v,P,w)=\bar\pi,\qquad \Pi(v,P,w)=V(v,P)=\frac{\bar\mu}r-c\,\frac{\mathbb E[\int_0^\tau a_te^{-rt}dt]}{1-\mathbb E[e^{-r\tau}]}-L\,\frac{\mathbb E[\int_0^\tau N^{a}_te^{-rt}dt]}{1-\mathbb E[e^{-r\tau}]}-\frac K{e^{r/v}-1}.
--   $$
--
--   This is the reduction of the principal's problem to the maximization of $V_I(v,P)$ over $v$ and $P$, on which all later results rest.
--
--   **Formalization Note** The hypothesis on the laws is what the paper's three policies satisfy and what makes $1-\mathbb E[e^{-r\tau}]>0$; the statement is posed for every such policy so that it covers $H(q)$ for every $q$.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 10, §3.2, paragraph before Assumption 1, display (6)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.Hybrid

theorem binding_participation (p : OpRiskInspection.RandomVsPeriodic.Params) (hp : OpRiskInspection.RandomVsPeriodic.Standing p) (K : ℝ) (hK : 0 < K)
    (law : ℝ → MeasureTheory.Measure ℝ)
    (hlaw : ∀ v, 0 < v →
      MeasureTheory.IsProbabilityMeasure (law v) ∧ law v (Set.Iic 0) = 0)
    (v P w : ℝ) (a : OpRiskInspection.RandomVsPeriodic.Effort) (hv : 0 < v) (hP : 0 ≤ P) (hw : 0 ≤ w)
    (ha : OpRiskInspection.RandomVsPeriodic.AgentOptimal p (law v) P a)
    (hpart : p.pibar ≤ OpRiskInspection.RandomVsPeriodic.agentPayoff p (law v) a P w)
    (hopt : ∀ x, OpRiskInspection.RandomVsPeriodic.Achievable p K law x → x ≤ OpRiskInspection.RandomVsPeriodic.principalPayoff p K v (law v) a P w) :
    OpRiskInspection.RandomVsPeriodic.agentPayoff p (law v) a P w = p.pibar ∧
      OpRiskInspection.RandomVsPeriodic.principalPayoff p K v (law v) a P w = OpRiskInspection.RandomVsPeriodic.reducedPayoff p K v (law v) a := by sorry

end OpRiskInspection.Hybrid
