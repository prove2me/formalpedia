-- Prove2me | Theorems.Thm_KellyLossNetworks_Routing_union_bound
-- name    : KellyLossNetworks.Routing.union_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:48.608723+00:00
-- url     : https://prove2.me/theorems/fd680eee-b689-4635-88d0-26a50f3bacf5
-- title:
--   Proof of Thm 4.45, p. 359 — 1 − P(K) ≤ ½K(K − 1)(P₁ + P₂) over the ½K(K − 1) edges
-- statement:
--   Let $X\ge 0$ be a random variable with law $\mu$, $m=\mathbb E(C-X)^+$ and $0<\varepsilon<m^2$. For $K\ge 3$ nodes, let $P(K)$ be the probability that i.i.d. loads with law $\mu$ on the edges of the complete graph on $K$ nodes can be carried over direct and two-edge routes within capacity $C$, and let $P_1(K-2)$, $P_2(K-2)$ be the probabilities of (4.48) and (4.49) with $n=K-2$. Then
--   $$
--   1-P(K)\le \tfrac12 K(K-1)\,\big(P_1(K-2)+P_2(K-2)\big).
--   $$
--   Combined with (4.48) and (4.49), the right-hand side is at most $\tfrac12K(K-1)\,(e^{-(K-2)I_1}+e^{-(K-2)I_2})\to 0$, which gives Theorem 4.45.
--
--   **Formalization Note.** The inequality is in $[0,\infty]$; $P(K)$ is the outer measure of the routing event.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 359, §4.6, proof of Theorem 4.45 (last sentence)

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace KellyLossNetworks.Routing

/-- **The union bound over the ½K(K - 1) edges.** Let `X ≥ 0` have law `μ`, `m = 𝔼(C - X)⁺` and
`0 < ε < m²`. For `K ≥ 3` nodes,
`1 - P(K) ≤ ½K(K - 1) · (P₁ + P₂)` with `P₁ = ℙ{∑ (K - 2)⁻¹ Y_i < 1}` and
`P₂ = ℙ{∑ (K - 2)⁻¹ Z_i > 1}` over `K - 2` independent copies.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, proof of Theorem 4.45, p. 359 ("Since there are just ½K(K - 1) edges in the network, the
bounds (4.48) and (4.49) imply that P(K) → 1 as K → ∞"). -/
theorem union_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C ε : ℝ) (hε : 0 < ε) (hεm : ε < spareMean μ C ^ 2) (K : ℕ) (hK : 3 ≤ K) :
    1 - routingProb μ C K ≤
      (K : ENNReal) * ((K : ENNReal) - 1) / 2 * (P1 μ C ε (K - 2) + P2 μ C ε (K - 2)) := by sorry

end KellyLossNetworks.Routing
