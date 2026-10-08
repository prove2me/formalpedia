-- Prove2me | Theorems.Thm_MitigateSupplyRisk_DualSourcing_lemma_1
-- name    : MitigateSupplyRisk.DualSourcing.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:10.461166+00:00
-- url     : https://prove2.me/theorems/6ab95a20-b12f-4ada-bc66-bd88749135a3
-- title:
--   Lemma 1, p. 494 — Π₂(q; a) is submodular in q
-- statement:
--   Consider the two-supplier random-capacity newsvendor: suppliers $i = 1, 2$ with design capacities $K_i$, independent continuous capacity losses $\xi_i$ with laws $\nu_i(a_i)$, deliveries $y_i = \min\{q_i, (K_i - \xi_i)^+\}$, and a demand $X \ge 0$ with finite mean, independent of the losses. Let $\Pi_2(q; a)$ be the expected profit of the order vector $q = (q_1, q_2)$ at reliability indices $a$.
--
--   Then $\Pi_2(\cdot\,; a)$ is submodular on the quadrant $q \ge 0$: for all $q, q' \ge 0$,
--   $$\Pi_2(q \vee q'; a) + \Pi_2(q \wedge q'; a) \le \Pi_2(q; a) + \Pi_2(q'; a),$$
--   where $\vee$ and $\wedge$ are the componentwise maximum and minimum.
--
--   Submodularity says the two order quantities are substitutes: a larger order from one supplier lowers the marginal value of ordering from the other. The paper uses it to read off the direction of the optimal orders in the later results.
--
--   **Formalization Note.** The paper does not define "submodular"; the lattice inequality above is the standard definition, equivalent to $\partial^2 \Pi_2 / \partial q_1 \partial q_2 \le 0$ for twice differentiable functions, and needs no differentiability. The statement holds for every nonnegative demand law with finite mean (no density is assumed).
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 494 (PDF p. 6), Lemma 1

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model

open MeasureTheory ProbabilityTheory

namespace MitigateSupplyRisk.DualSourcing

/-- Lemma 1 (Wang, Gilland, Tomlin 2010, p. 494): the second-stage expected profit `Π₂(q; a)` is
submodular in the order vector `q` on the feasible quadrant `q ≥ 0`, in the lattice form
`Π₂(q ∨ q') + Π₂(q ∧ q') ≤ Π₂(q) + Π₂(q')` (componentwise max and min). Demand is any nonnegative
law with finite mean; no density is needed. -/
theorem lemma_1 (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (a : Fin 2 → ℝ)
    (q q' : Fin 2 → ℝ) (hq : q ∈ Model.orders) (hq' : q' ∈ Model.orders) :
    M.Pi2 μ (q ⊔ q') a + M.Pi2 μ (q ⊓ q') a ≤ M.Pi2 μ q a + M.Pi2 μ q' a := by sorry

end MitigateSupplyRisk.DualSourcing
