-- Prove2me | Theorems.Thm_MitigateSupplyRisk_DualSourcing_lemma_2b
-- name    : MitigateSupplyRisk.DualSourcing.lemma_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:05.881183+00:00
-- url     : https://prove2.me/theorems/ed2f213d-5800-4ff6-bb42-c8dbc0d1a683
-- title:
--   Lemma 2(b), p. 494 — Π₂*(a) is increasing in supplier i's reliability index
-- statement:
--   Consider the two-supplier random-capacity newsvendor, with demand $X \ge 0$ of finite mean, and let
--   $$\Pi_2^*(a) = \sup_{q \ge 0} \Pi_2(q; a)$$
--   be the optimal second-stage expected profit at reliability indices $a = (a_1, a_2)$. Recall that a larger index $a_i$ makes supplier $i$'s capacity loss stochastically smaller.
--
--   Then, for each supplier $i$ and with the other supplier's index held fixed, $\Pi_2^*$ is (weakly) increasing in $a_i$:
--   $$a_i \le \hat a_i \implies \Pi_2^*(a_i, a_j) \le \Pi_2^*(\hat a_i, a_j).$$
--
--   A more reliable supplier never hurts the firm once it re-optimizes its orders. This is the value of reliability that the process-improvement strategy of the paper buys.
--
--   **Formalization Note.** "Increasing" is weak, as the paper declares on p. 492. The statement is for any demand law (no density) and any committed costs $\eta_i \in [0,1]$.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 494 (PDF p. 6), Lemma 2(b)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model

open MeasureTheory ProbabilityTheory

namespace MitigateSupplyRisk.DualSourcing

/-- Lemma 2(b) (Wang, Gilland, Tomlin 2010, p. 494): the optimal second-stage expected profit
`Π₂*(a) = sup_{q ≥ 0} Π₂(q; a)` is (weakly) increasing in supplier `i`'s reliability index `a_i`,
the other supplier's index held fixed. Demand is any nonnegative law with finite mean. -/
theorem lemma_2b (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (i : Fin 2) (a : Fin 2 → ℝ) :
    Monotone (fun t : ℝ => M.Pi2star μ (Function.update a i t)) := by sorry

end MitigateSupplyRisk.DualSourcing
