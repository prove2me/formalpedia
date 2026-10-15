-- Prove2me | Theorems.Thm_OpRiskInspection_RandomVsPeriodic_periodic_regimes
-- name    : OpRiskInspection.RandomVsPeriodic.periodic_regimes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:28.267758+00:00
-- url     : https://prove2.me/theorems/6dfffbba-db2b-4846-857f-64c4b005f0e4
-- title:
--   §4.2, p. 14, (EC.4) — periodic-policy payoff regimes
-- statement:
--   Let $V_D(v,P)$ be the reduced principal payoff under periodic inspection at an optimal agent effort. For $K,v>0$ and $P\ge0$, it has the three branches in (EC.4):
--   $$V_D(v,P)=\begin{cases}\bar V_D(v,P),&P>c/\lambda\text{ and }v>\underline v_D,\\\underline V_D(v,P),&P>c/\lambda\text{ and }v\le\underline v_D,\\V_D^0(v),&P\le c/\lambda.\end{cases}$$
--   The explicit functions $\bar V_D$, $\underline V_D$, and $V_D^0$ are defined separately from (EC.4). The middle branch captures effort that begins only late in the cycle.
--
--   **Formalization Note** The statement quantifies over any optimal admissible effort path; only its values in the inspection cycle affect the payoff.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 14, §4.2, first payoff paragraph; p. ec6, (EC.4)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_ClosedForms

namespace OpRiskInspection.RandomVsPeriodic

/-- §4.2, p. 14, and (EC.4), p. ec6: the three periodic-policy payoff branches. -/
theorem periodic_regimes (p : Params) (hp : Standing p)
    (K v P : ℝ) (hK : 0 < K) (hv : 0 < v) (hP : 0 ≤ P)
    (a : Effort) (ha : AgentOptimal p (periodicLaw v) P a) :
    (p.c / p.lam < P → vD p P < v →
      reducedPayoff p K v (periodicLaw v) a = VbarD p K v P) ∧
    (p.c / p.lam < P → v ≤ vD p P →
      reducedPayoff p K v (periodicLaw v) a = VunderD p K v P) ∧
    (P ≤ p.c / p.lam →
      reducedPayoff p K v (periodicLaw v) a = V0D p K v) := by sorry

end OpRiskInspection.RandomVsPeriodic
