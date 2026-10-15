-- Prove2me | Theorems.Thm_OpRiskInspection_RandomVsPeriodic_proposition_4
-- name    : OpRiskInspection.RandomVsPeriodic.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:57.232685+00:00
-- url     : https://prove2.me/theorems/99d0c588-e234-4432-bd99-4b9f2d48c8a0
-- title:
--   Proposition 4, p. 17 — the random-periodic ranking reverses at an inspection-cost threshold
-- statement:
--   In the model of §3 under Assumption 1, there is an inspection-cost threshold $K_{RD}$, depending on the model parameters and independent of the particular cost $K$, such that
--   $$0<K<K_{RD}\implies \Pi_R(S_R^*)<\Pi_D(S_D^*),$$
--   $$0<K\text{ and }K>K_{RD}\implies \Pi_D(S_D^*)<\Pi_R(S_R^*).$$
--   Here $S_R^*$ and $S_D^*$ are optimal feasible principal strategies under random and periodic inspection. Thus periodic inspection yields the strictly greater optimal payoff at low inspection cost, while random inspection does so at high cost.
--
--   **Formalization Note** Each comparison asserts that the better policy has an achievable payoff greater than every achievable payoff under the other policy. This avoids an empty or unbounded real supremum. The source does not explicitly assert $K_{RD}>0$, so no positivity condition is imposed on it; $K$ itself is positive.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 17, Proposition 4; proof pp. ec30–ec33

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.RandomVsPeriodic

/-- Proposition 4, p. 17: a cost threshold reverses the ranking of the policies. -/
theorem proposition_4 (p : Params) (hp : Standing p) :
    ∃ KRD : ℝ,
      (∀ K, 0 < K → K < KRD →
        ∃ xD, Achievable p K periodicLaw xD ∧
          ∀ xR, Achievable p K randomLaw xR → xR < xD) ∧
      (∀ K, 0 < K → KRD < K →
        ∃ xR, Achievable p K randomLaw xR ∧
          ∀ xD, Achievable p K periodicLaw xD → xD < xR) := by sorry

end OpRiskInspection.RandomVsPeriodic
