-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Improvement_lemma_2b_single
-- name    : MitigateSupplyRisk.Improvement.lemma_2b_single
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:02.88092+00:00
-- url     : https://prove2.me/theorems/e16387e8-d253-4ab3-9d18-a9cbc22447b9
-- title:
--   Lemma 2(b), p. 494 (single-supplier instance) — Π₂*(a) is increasing in the reliability index
-- statement:
--   In the single-supplier model, assume the unit cost is nonnegative, $c \ge 0$. Then the optimal second-stage profit
--   $$\Pi_2^*(a) = \sup_{q \ge 0} \Pi_2(q; a)$$
--   is a (weakly) increasing function of the reliability index $a$:
--   $$a \le a' \implies \Pi_2^*(a) \le \Pi_2^*(a').$$
--
--   A more reliable supplier (a stochastically smaller capacity loss) can never hurt the firm once it orders optimally. The result is the source of the term $\theta\,\Pi_2^*(a)$ in the first-stage profit being increasing in $a$, which drives the comparative statics of Corollary 2.
--
--   **Formalization Note** The paper states Lemma 2 for dual sourcing and applies all results of §4.1 to single sourcing (p. 496); this is the single-supplier instance, for every committed cost $\eta \in [0,1]$. The hypothesis $c \ge 0$ (the paper's reading of a cost) makes $\psi \le 0$, so the supremum is finite; with $c < 0$ and $\eta > 0$ the profit would be unbounded in $q$.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 494 (PDF 6), Lemma 2(b); p. 496 (PDF 8), §4.2.1

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model

open MeasureTheory ProbabilityTheory Set

namespace MitigateSupplyRisk.Improvement

theorem lemma_2b_single (M : Model) (hM : M.Assumptions) (hc : 0 ≤ M.c) :
    Monotone M.Pi2star := by sorry

end MitigateSupplyRisk.Improvement
