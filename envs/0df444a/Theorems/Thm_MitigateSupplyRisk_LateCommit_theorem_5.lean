-- Prove2me | Theorems.Thm_MitigateSupplyRisk_LateCommit_theorem_5
-- name    : MitigateSupplyRisk.LateCommit.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:30.278751+00:00
-- url     : https://prove2.me/theorems/a4d70963-ea0e-458e-9816-4762f100b384
-- title:
--   Theorem 5, p. 498 — identical suppliers except c₁ ≤ c₂: Π₁*ᴸ > Π₁*ᴱ if [Π₂*(a₂^{*E}) − Π₂*(a₁⁰)]⁺ > m z(a₂^{*E})/(θ(1 − θ))
-- statement:
--   Let suppliers 1 and 2 be identical except for their unit costs, with $c_1\le c_2$. Write $\theta$, $m$, $z$ and $a^0$ for their common success probability, unit improvement cost, effort function and initial reliability index, and assume $0<\theta<1$. Let $a_2^{*E}\ge a^0$ maximize supplier 2's early-commitment profit $\Pi_{12}^E$ over $a\ge a^0$. If
--   $$\bigl[P_2(a_2^{*E})-P_1(a_1^0)\bigr]^+>\frac{m\,z(a_2^{*E})}{\theta(1-\theta)},$$
--   where $P_2$ and $P_1$ are the single-sourcing values $\Pi_2^*$ of supplier 2 and supplier 1, then late commitment strictly outperforms early commitment:
--   $$\Pi_1^{*L}>\Pi_1^{*E}.$$
--
--   The condition says that the expected-profit gain from switching to the improved, costlier supplier 2 in the event "supplier 2 succeeds, supplier 1 fails", which has probability $\theta(1-\theta)$, outweighs the cost of improving supplier 2. It quantifies the value of keeping the supplier choice open.
--
--   **Formalization Note** The hypothesis $0<\theta<1$ is added. The printed condition divides by $\theta(1-\theta)$, and the paper notes (p. 497) that late commitment has no value at $\theta=1$; in Lean $x/0=0$, so at $\theta\in\{0,1\}$ the condition would read $[\cdot]^+>0$ and the conclusion would be false. The maximizer $a_2^{*E}$ is assumed, not claimed to exist, and $\Pi_1^{*L}$, $\Pi_1^{*E}$ are suprema, not assumed to be attained. The common data are read from supplier 2's record, which equals supplier 1's.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 498 (PDF p. 10), Theorem 5

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

namespace MitigateSupplyRisk.LateCommit

/-- Theorem 5 (p. 498): let suppliers 1 and 2 be identical except for their unit costs, with
`c₁ ≤ c₂`, and write `θ, m, z` for the common improvement data, with `0 < θ < 1`.  If
`a₂^{*E}` maximizes supplier 2's early-commitment profit over `a ≥ a⁰` and
`[Π₂*(a₂^{*E}) − Π₂*(a₁⁰)]⁺ > m z(a₂^{*E}) / (θ(1 − θ))` (the `Π₂*` terms being supplier 2's and
supplier 1's single-sourcing values), then `Π₁^{*L} > Π₁^{*E}`. -/
theorem theorem_5 (X : Setting) (hid : X.IdenticalExceptCost) (hc : X.c₁ ≤ X.c₂)
    (hθ₀ : 0 < X.I₂.θ) (hθ₁ : X.I₂.θ < 1)
    {a₂E : ℝ} (ha₂E : X.I₂.a0 ≤ a₂E) (hmax : IsMaxOn X.early₂ (Set.Ici X.I₂.a0) a₂E)
    (hgain : X.I₂.m * X.I₂.z a₂E / (X.I₂.θ * (1 - X.I₂.θ)) < max (X.P₂ a₂E - X.P₁ X.I₁.a0) 0) :
    X.earlyValue < X.lateValue := by sorry

end MitigateSupplyRisk.LateCommit
