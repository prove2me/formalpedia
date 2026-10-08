-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Improvement_corollary_2b
-- name    : MitigateSupplyRisk.Improvement.corollary_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:55.904914+00:00
-- url     : https://prove2.me/theorems/ad9805ec-fed9-4304-a936-663c0218e5bb
-- title:
--   Corollary 2(b), p. 497 — the optimal improvement effort is increasing in the success probability θ
-- statement:
--   Fix the single-supplier model with unit cost $c \ge 0$ and the improvement data except the success probability, and write $\Pi_1^{\theta}$ for the first-stage profit (7) with success probability $\theta$. Let $0 \le \theta_1 \le \theta_2 \le 1$, let $a_1 \ge a^0$ maximize $\Pi_1^{\theta_1}$ and $a_2 \ge a^0$ maximize $\Pi_1^{\theta_2}$ over $[a^0,\infty)$. Then
--   $$\max\{a_1, a_2\} \text{ maximizes } \Pi_1^{\theta_2} \quad\text{and}\quad \min\{a_1, a_2\} \text{ maximizes } \Pi_1^{\theta_1}$$
--   over $[a^0, \infty)$: the optimal reliability index, and hence the optimal effort, increases in $\theta$ in the strong set order.
--
--   A more likely successful improvement project justifies a more ambitious reliability target.
--
--   **Formalization Note** Stated in the strong set order on the argmax, as for Corollary 2(a). The hypothesis $c \ge 0$ is the paper's reading of a cost; it makes $\Pi_2^*$ finite and increasing in the index (Lemma 2(b)). The statement holds for every committed cost $\eta$.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 497 (PDF 9), Corollary 2(b)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model
import Definitions.Def_MitigateSupplyRisk_Improvement_FirstStage

open MeasureTheory ProbabilityTheory Set

namespace MitigateSupplyRisk.Improvement

theorem corollary_2b (M : Model) (I : Effort) (hM : M.Assumptions) (hI : I.Assumptions)
    (hc : 0 ≤ M.c) (θ₁ θ₂ : ℝ) (hθ₁ : 0 ≤ θ₁) (hθ : θ₁ ≤ θ₂) (hθ₂ : θ₂ ≤ 1) (a₁ a₂ : ℝ)
    (ha₁ : a₁ ∈ Ici I.a0) (h₁ : IsMaxOn (Pi1 M { I with θ := θ₁ }) (Ici I.a0) a₁)
    (ha₂ : a₂ ∈ Ici I.a0) (h₂ : IsMaxOn (Pi1 M { I with θ := θ₂ }) (Ici I.a0) a₂) :
    IsMaxOn (Pi1 M { I with θ := θ₂ }) (Ici I.a0) (max a₁ a₂) ∧
    IsMaxOn (Pi1 M { I with θ := θ₁ }) (Ici I.a0) (min a₁ a₂) := by sorry

end MitigateSupplyRisk.Improvement
