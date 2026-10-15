-- Prove2me | Theorems.Thm_OpRiskInspection_RandomVsPeriodic_reduction_6
-- name    : OpRiskInspection.RandomVsPeriodic.reduction_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:52.266873+00:00
-- url     : https://prove2.me/theorems/26cd7c80-c5a4-4fef-96b1-c5cf0640a399
-- title:
--   §3.2, p. 10 — binding participation gives reduced payoff (6)
-- statement:
--   Fix the paper's standing parameters, an inspection cost $K>0$, a frequency $v>0$, an inspection-interval law $F$, a penalty $P$, a wage $w$, and an optimal effort path $a$. If the agent's participation constraint binds, $\pi_F(a;P,w)=\bar\pi$, then the principal's payoff (3) equals the reduced payoff (6):
--   $$\Pi_F(v,P,w;a)=V_F(v,P;a).$$
--   This equality removes the wage from the principal's objective at a binding feasible strategy and is the algebraic reduction used in the policy comparisons.
--
--   **Formalization Note** The statement gives the equality under binding participation. The preceding prose's claim that every optimum binds is a separate optimization claim, not assumed here.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 10, §3.2 and (6)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.RandomVsPeriodic

/-- Equation (6), p. 10, under the binding participation constraint (5). -/
theorem reduction_6 (p : Params) (hp : Standing p) (K v P w : ℝ)
    (F : MeasureTheory.Measure ℝ) (a : Effort)
    (hv : 0 < v) (hK : 0 < K) (ha : AgentOptimal p F P a)
    (hbind : agentPayoff p F a P w = p.pibar) :
    principalPayoff p K v F a P w = reducedPayoff p K v F a := by sorry

end OpRiskInspection.RandomVsPeriodic
