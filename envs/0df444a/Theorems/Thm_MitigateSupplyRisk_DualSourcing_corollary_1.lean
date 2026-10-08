-- Prove2me | Theorems.Thm_MitigateSupplyRisk_DualSourcing_corollary_1
-- name    : MitigateSupplyRisk.DualSourcing.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:43.18881+00:00
-- url     : https://prove2.me/theorems/25d539fb-a789-4fdb-a4d0-752e6b954bc3
-- title:
--   Corollary 1, p. 496 — the quantity hedge region and size shrink, and Ω₁ expands in a₁⁰ and contracts in a₂⁰
-- statement:
--   Work in the setting of Theorem 2: deterministic demand, no committed cost ($\eta_1 = \eta_2 = 0$), $0 < \phi_i < 1$, $G_i(K_i, a) = 1$ for every reliability index $a$, and $\phi_1 \ge \phi_2$. Let $\Omega_1(a)$ be the single-sourcing region, $\Omega_3 \cup \Omega_4 \cup \Omega_5\,(a)$ the quantity-hedge region, and $q_1^*(a, x) + q_2^*(a, x)$ the optimal total order of Theorem 2 at reliability indices $a$ and demand $x$.
--
--   Raise one supplier's reliability index from $s$ to $s' \ge s$, keeping the other index fixed. Then:
--
--   1. (a) the quantity-hedge region contracts, $\Omega_3 \cup \Omega_4 \cup \Omega_5\,(a') \subseteq \Omega_3 \cup \Omega_4 \cup \Omega_5\,(a)$, and for every demand $x \ge 0$ the quantity hedge size does not increase:
--   $$[q_1^*(a', x) + q_2^*(a', x) - x]^+ \le [q_1^*(a, x) + q_2^*(a, x) - x]^+;$$
--   2. (b) the single-sourcing region expands when supplier 1's index is raised, $\Omega_1(a) \subseteq \Omega_1(a')$, and contracts when supplier 2's index is raised, $\Omega_1(a') \subseteq \Omega_1(a)$.
--
--   As suppliers become more reliable, the firm has less need to over-order to hedge against capacity shortfalls.
--
--   **Formalization Note.** The regions and total order are those of Theorem 2 with corrected bounds; the hedge region $\Omega_3 \cup \Omega_4 \cup \Omega_5$ is unchanged by the correction. Under $G_i(K_i) = 1$ the labelling hypothesis $\phi_1 G_1(K_1) \ge \phi_2 G_2(K_2)$ of Theorem 2 reads $\phi_1 \ge \phi_2$, and the upper end $K_1 - G_1^{-1}(\tfrac{\phi_2}{\phi_1} G_2(K_2))$ of $\Omega_1$ does not depend on $a_2$, so the contraction in $a_2$ holds with equality. Strict increase of $G_i$ is not needed for these statements and is not assumed.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 496 (PDF p. 8), Corollary 1

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Regions

open MeasureTheory ProbabilityTheory

namespace MitigateSupplyRisk.DualSourcing

/-- Corollary 1 (Wang, Gilland, Tomlin 2010, p. 496), in the setting of Theorem 2 (`η = 0`,
`0 < φ_i < 1`, `G_i(K_i, a) = 1` at every reliability index, and `φ₁ ≥ φ₂`, which is the
ordering `φ₁ G₁(K₁) ≥ φ₂ G₂(K₂)` under `G_i(K_i) = 1`). Raise supplier `i`'s reliability index
from `s` to `s' ≥ s`, the other index fixed. Then
(a) the quantity-hedge region `Ω₃ ∪ Ω₄ ∪ Ω₅` contracts, and for every demand `x ≥ 0` the hedge
size `[q₁* + q₂* − x]⁺` of Theorem 2's optimal vector does not increase;
(b) the single-sourcing region `Ω₁` expands when `i` is supplier 1 and contracts when `i` is
supplier 2. -/
theorem corollary_1 (M : Model)
    (hη : ∀ i, M.η i = 0)
    (hφpos : ∀ i, 0 < M.phi i) (hφlt : ∀ i, M.phi i < 1)
    (hGK : ∀ i a, M.G i (M.K i) a = 1)
    (hord : M.phi 1 ≤ M.phi 0)
    (i : Fin 2) (a : Fin 2 → ℝ) (s s' : ℝ) (hss' : s ≤ s') :
    -- (a) the hedge region contracts
    M.hedgeRegion (Function.update a i s') ⊆ M.hedgeRegion (Function.update a i s) ∧
    -- (a) the hedge size decreases
    (∀ x : ℝ, 0 ≤ x →
      max (M.qstarTotal (Function.update a i s') x - x) 0 ≤
        max (M.qstarTotal (Function.update a i s) x - x) 0) ∧
    -- (b) Ω₁ expands as supplier 1's index increases
    (i = 0 → M.singleRegion (Function.update a i s) ⊆ M.singleRegion (Function.update a i s')) ∧
    -- (b) Ω₁ contracts as supplier 2's index increases
    (i = 1 → M.singleRegion (Function.update a i s') ⊆ M.singleRegion (Function.update a i s)) := by sorry

end MitigateSupplyRisk.DualSourcing
