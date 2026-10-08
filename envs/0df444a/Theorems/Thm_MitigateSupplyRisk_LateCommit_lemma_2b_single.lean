-- Prove2me | Theorems.Thm_MitigateSupplyRisk_LateCommit_lemma_2b_single
-- name    : MitigateSupplyRisk.LateCommit.lemma_2b_single
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:35.847397+00:00
-- url     : https://prove2.me/theorems/8eb150e0-d451-45dc-91df-6d77e6b7c383
-- title:
--   Lemma 2(b), p. 494 — single sourcing: Π₂*(a) is increasing in the reliability index a
-- statement:
--   Consider single sourcing from one unreliable supplier with unit cost $c\ge 0$ in the model of this mission. The optimal second-stage expected profit $\Pi_2^*(a)=\sup_{q\ge 0}\Pi_2(q;a)$ is (weakly) increasing in the supplier's reliability index:
--   $$a\le a'\ \Longrightarrow\ \Pi_2^*(a)\le\Pi_2^*(a').$$
--
--   This is the single-supplier instance of Lemma 2(b). It is the monotonicity that the comparison of late and early commitment relies on (Lemma 4 and the no-value statement of §4.2.2).
--
--   **Formalization Note** The paper states Lemma 2 for the dual-sourcing model of §4.1. Here the other supplier is absent, which the paper (p. 496) treats as the special case where that supplier has infinite cost. "Increasing" is weak, following the paper's convention (p. 492). Monotonicity is stated over all real indices, because the loss family is ordered for all of them. The hypothesis $c\ge 0$ is the paper's reading of a unit cost.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 494 (PDF p. 6), Lemma 2(b), single-supplier instance (cf. p. 496, §4.2.1)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

namespace MitigateSupplyRisk.LateCommit

/-- Lemma 2(b), single-supplier instance (p. 494): the optimal single-sourcing second-stage
profit `Π₂*(a) = sup_{q ≥ 0} Π₂(q; a)` is (weakly) increasing in the reliability index `a`. -/
theorem lemma_2b_single (M : Market) (S : Supplier) (c : ℝ) (hc : 0 ≤ c) :
    Monotone (fun a => optValue M S c a) := by sorry

end MitigateSupplyRisk.LateCommit
