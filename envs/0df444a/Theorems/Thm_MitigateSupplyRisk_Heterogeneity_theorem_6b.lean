-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Heterogeneity_theorem_6b
-- name    : MitigateSupplyRisk.Heterogeneity.theorem_6b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:58.366994+00:00
-- url     : https://prove2.me/theorems/fb7b1527-7cc3-46e3-8b5c-49034712f0c6
-- title:
--   Theorem 6(b), p. 501 — Π*_DS is increasing in the cost and committed-cost heterogeneity Δ_c, Δ_η
-- statement:
--   Consider two suppliers that are identical in every attribute except one, as in Theorem 6(a), and let $\Pi^*_{DS} = \Pi_2^*(a^0, a^0) = \sup_{q \ge 0} \Pi_2(q; a^0, a^0)$ be the optimal expected profit of dual sourcing without improvement.
--
--   1. **Cost heterogeneity.** With unit costs $c_1 = c - \Delta_c$ and $c_2 = c + \Delta_c$, $c > 0$, the value $\Pi^*_{DS}$ is nondecreasing in $\Delta_c$ on $[0, c)$.
--   2. **Committed-cost heterogeneity.** With common unit cost $c$ and committed costs $\eta_1 = \eta - \Delta_\eta$, $\eta_2 = \eta + \Delta_\eta$, the value $\Pi^*_{DS}$ is nondecreasing in $\Delta_\eta$ on $[0, \min\{\eta, 1-\eta\}]$.
--
--   In each case
--   $$0 \le \Delta \le \Delta' \implies \Pi^*_{DS}(\Delta) \le \Pi^*_{DS}(\Delta').$$
--
--   That dual sourcing also benefits from heterogeneity is less obvious than for single sourcing: one supplier becomes more attractive while the other becomes less so, and directing more of the order to the cheaper supplier weakens the diversification that dual sourcing provides.
--
--   **Formalization Note** "Increasing" is in the weak sense (p. 492). The standing assumptions of the model are the fields of `SymData.Standing`. The clause of Theorem 6(b) on reliability heterogeneity $\Delta_a$ under uniformly distributed capacity loss is not stated here.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 501 (PDF 13), Theorem 6(b), Δ_c and Δ_η parts

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Heterogeneity_Model

namespace MitigateSupplyRisk.Heterogeneity
theorem theorem_6b (S : SymData) (hS : S.Standing) :
    MonotoneOn (fun Δ => (S.costModel Δ).PiDS) (Set.Ico 0 S.c) ∧
    MonotoneOn (fun Δ => (S.etaModel Δ).PiDS) (Set.Icc 0 (min S.η (1 - S.η))) := by sorry
end MitigateSupplyRisk.Heterogeneity
