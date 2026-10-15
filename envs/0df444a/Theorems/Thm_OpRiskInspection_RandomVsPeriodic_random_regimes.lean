-- Prove2me | Theorems.Thm_OpRiskInspection_RandomVsPeriodic_random_regimes
-- name    : OpRiskInspection.RandomVsPeriodic.random_regimes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:32.233609+00:00
-- url     : https://prove2.me/theorems/af9a4a73-3ddc-4e0f-b2ee-5bee5c61eb34
-- title:
--   §4.2, p. 14, (EC.2) — random-policy payoff regimes
-- statement:
--   Let $V_R(v,P)$ be the reduced principal payoff under random inspection at an optimal agent effort. For $K,v>0$ and $P\ge0$, it has the branches given in (EC.2):
--   $$V_R(v,P)=\begin{cases}\bar V_R(v,P),&P>c/\lambda\text{ and }v>\underline v_R,\\V_R^0(v),&P>c/\lambda\text{ and }v\le\underline v_R,\\V_R^0(v),&P\le c/\lambda.\end{cases}$$
--   The explicit functions $\bar V_R$ and $V_R^0$ are defined separately from (EC.2). This regime split connects the agent's effort threshold in Lemma 3 to the principal's objective.
--
--   **Formalization Note** The statement quantifies over any optimal admissible effort path; the path's values outside null sets do not change the payoff.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 14, §4.2, first payoff paragraph; p. ec5, (EC.2)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_ClosedForms

namespace OpRiskInspection.RandomVsPeriodic

/-- §4.2, p. 14, and (EC.2), p. ec5: the two random-policy payoff branches. -/
theorem random_regimes (p : Params) (hp : Standing p)
    (K v P : ℝ) (hK : 0 < K) (hv : 0 < v) (hP : 0 ≤ P)
    (a : Effort) (ha : AgentOptimal p (randomLaw v) P a) :
    (p.c / p.lam < P → vR p P < v →
      reducedPayoff p K v (randomLaw v) a = VbarR p K v P) ∧
    (p.c / p.lam < P → v ≤ vR p P →
      reducedPayoff p K v (randomLaw v) a = V0R p K v) ∧
    (P ≤ p.c / p.lam →
      reducedPayoff p K v (randomLaw v) a = V0R p K v) := by sorry

end OpRiskInspection.RandomVsPeriodic
