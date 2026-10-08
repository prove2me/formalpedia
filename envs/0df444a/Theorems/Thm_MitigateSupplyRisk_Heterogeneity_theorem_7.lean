-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Heterogeneity_theorem_7
-- name    : MitigateSupplyRisk.Heterogeneity.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:41.251028+00:00
-- url     : https://prove2.me/theorems/29cf98ba-6249-4397-9818-2e8b93fa6277
-- title:
--   Theorem 7, p. 502 — Π*_SSI − Π*_DS is increasing in the cost heterogeneity Δ_c
-- statement:
--   Consider two suppliers that are identical in every attribute (revenue $r$, salvage $v$, penalty $p$, committed cost $\eta$, capacity $K$, capacity-loss distributions $G(\cdot, a)$, initial reliability $a^0$, success probability $\theta$, effort cost $m$, effort function $z$) except in unit cost, with
--   $$c_1 = c - \Delta_c, \qquad c_2 = c + \Delta_c, \qquad 0 \le \Delta_c < c .$$
--   Let $\Pi^*_{SSI}(\Delta_c)$ be the optimal expected profit of single sourcing with improvement under early commitment (the firm picks one supplier, invests in improving it, and orders only from it), and $\Pi^*_{DS}(\Delta_c)$ the optimal expected profit of dual sourcing without improvement, both computed at these costs. Then
--   $$\Pi^*_{SSI}(\Delta_c) - \Pi^*_{DS}(\Delta_c) \ \text{ is nondecreasing in } \Delta_c \in [0, c).$$
--
--   Both strategies benefit from the cheaper supplier (Theorem 6), but dual sourcing is held back by the more expensive one, so single sourcing with improvement becomes increasingly preferred as the suppliers' costs diverge. The paper observes this in its numerical study (Figure 4(a)) and confirms it with this theorem.
--
--   **Formalization Note** "Increasing" is in the weak sense (p. 492). Both values are optimal values of the model, recomputed at each $\Delta_c$: suprema over all order quantities $q \ge 0$, all target indices $a \ge a^0$, and both choices of the single source. The standing assumptions of the model, including the disclosed readings $r, p \ge 0$, $c > 0$ and $v < r + p$, are the fields of `SymData.Standing`. No restriction $\eta = 0$ and no concavity of $G$ in $a$ is assumed; the paper states the theorem without them.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 502 (PDF 14), Theorem 7; definitions p. 500 (PDF 12), §5, and p. 501 (PDF 13), §5.1

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Heterogeneity_Model

namespace MitigateSupplyRisk.Heterogeneity
theorem theorem_7 (S : SymData) (hS : S.Standing) :
    MonotoneOn (fun Δ => (S.costModel Δ).PiSSI - (S.costModel Δ).PiDS) (Set.Ico 0 S.c) := by sorry
end MitigateSupplyRisk.Heterogeneity
