-- Prove2me | Theorems.Thm_OpRiskInspection_Hybrid_proposition_5
-- name    : OpRiskInspection.Hybrid.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:27.947738+00:00
-- url     : https://prove2.me/theorems/28857db2-bd67-4535-a66b-28fcbe4e17bb
-- title:
--   Proposition 5, p. 20 — the optimal hybrid payoff strictly beats the random optimum and weakly beats the periodic optimum
-- statement:
--   Under the standing assumptions and for every inspection cost $K>0$, there is a payoff $x_H$ achievable by some hybrid policy $H(q)$, $q\in[0,1]$, such that
--   $$
--   x_R<x_H\ \text{ for every achievable random payoff }x_R,\qquad x_D\le x_H\ \text{ for every achievable periodic payoff }x_D .
--   $$
--   In the paper's notation: $\Pi_{H(q^*)}(S^*_{H(q^*)})>\Pi_R(S^*_R)$ and $\Pi_{H(q^*)}(S^*_{H(q^*)})\ge\Pi_D(S^*_D)$.
--
--   A suitable mixture of periodic and random inspection is never worse than either pure policy, and strictly better than random inspection.
--
--   **Formalization Note** The optimal mix $q^*$ of (25) is not formalized, since its existence is not proved in the paper. One hybrid payoff that dominates both is exactly what the comparison with $\Pi_{H(q^*)}(S^*_{H(q^*)})$ asserts. The weak part is immediate in this encoding because $H(1)$ is the periodic policy, as the paper notes; the content is the strict part.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 20, Proposition 5; (25), p. 20; proof pp. ec34–ec35

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.Hybrid

theorem proposition_5 (p : OpRiskInspection.RandomVsPeriodic.Params) (hp : OpRiskInspection.RandomVsPeriodic.Standing p) (K : ℝ) (hK : 0 < K) :
    ∃ xH, OpRiskInspection.RandomVsPeriodic.AchievableHybrid p K xH ∧
      (∀ xR, OpRiskInspection.RandomVsPeriodic.Achievable p K OpRiskInspection.RandomVsPeriodic.randomLaw xR → xR < xH) ∧
      (∀ xD, OpRiskInspection.RandomVsPeriodic.Achievable p K OpRiskInspection.RandomVsPeriodic.periodicLaw xD → xD ≤ xH) := by sorry

end OpRiskInspection.Hybrid
