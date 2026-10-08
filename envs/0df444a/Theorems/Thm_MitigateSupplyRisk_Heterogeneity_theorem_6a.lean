-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Heterogeneity_theorem_6a
-- name    : MitigateSupplyRisk.Heterogeneity.theorem_6a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:53:06.562066+00:00
-- url     : https://prove2.me/theorems/1c1fc812-ac34-41b9-95b7-17d3fd1a0676
-- title:
--   Theorem 6(a), p. 501 — Π*_SSI is increasing in the cost and committed-cost heterogeneity Δ_c, Δ_η
-- statement:
--   Consider two suppliers that are identical in every attribute (revenue $r$, salvage $v$, penalty $p$, committed cost, capacity $K$, capacity-loss distributions $G(\cdot, a)$, initial reliability $a^0$, success probability $\theta$, effort cost $m$, effort function $z$) except one, and let $\Pi^*_{SSI}$ be the optimal expected profit of single sourcing with improvement under early commitment.
--
--   1. **Cost heterogeneity.** With unit costs $c_1 = c - \Delta_c$ and $c_2 = c + \Delta_c$, $c > 0$, the value $\Pi^*_{SSI}$ is nondecreasing in $\Delta_c$ on $[0, c)$.
--   2. **Committed-cost heterogeneity.** With common unit cost $c$ and committed costs $\eta_1 = \eta - \Delta_\eta$, $\eta_2 = \eta + \Delta_\eta$, the value $\Pi^*_{SSI}$ is nondecreasing in $\Delta_\eta$ on $[0, \min\{\eta, 1-\eta\}]$.
--
--   In each case
--   $$0 \le \Delta \le \Delta' \implies \Pi^*_{SSI}(\Delta) \le \Pi^*_{SSI}(\Delta').$$
--
--   Single sourcing with improvement uses only one supplier, so it gains when one supplier becomes more attractive, even though the other becomes less so. This is the first half of the comparison made in Theorem 7.
--
--   **Formalization Note** "Increasing" is in the weak sense (p. 492). The range $0 \le \Delta_\eta \le \min\{\eta, 1-\eta\}$ is the reading of "analogously" (p. 501) that keeps both committed costs in $[0,1]$. The standing assumptions of the model, including the disclosed readings $r, p \ge 0$, $c > 0$ and $v < r + p$, are the fields of `SymData.Standing`. The parts of Theorem 6(a) on capacity heterogeneity $\Delta_K$ and reliability heterogeneity $\Delta_a$ are not stated here: the paper does not say how the improvement function depends on the initial reliability when the suppliers' indices differ.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 501 (PDF 13), Theorem 6(a), Δ_c and Δ_η parts

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Heterogeneity_Model

namespace MitigateSupplyRisk.Heterogeneity
theorem theorem_6a (S : SymData) (hS : S.Standing) :
    MonotoneOn (fun Δ => (S.costModel Δ).PiSSI) (Set.Ico 0 S.c) ∧
    MonotoneOn (fun Δ => (S.etaModel Δ).PiSSI) (Set.Icc 0 (min S.η (1 - S.η))) := by sorry
end MitigateSupplyRisk.Heterogeneity
