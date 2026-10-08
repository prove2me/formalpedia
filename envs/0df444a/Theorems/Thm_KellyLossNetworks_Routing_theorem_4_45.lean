-- Prove2me | Theorems.Thm_KellyLossNetworks_Routing_theorem_4_45
-- name    : KellyLossNetworks.Routing.theorem_4_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:51.59028+00:00
-- url     : https://prove2.me/theorems/fd0a4050-f644-4328-b496-f4395a4c9488
-- title:
--   Theorem 4.45 — if 𝔼e^{λX} < ∞ and 2𝔼(X − C)⁺ < 𝔼(C − X)⁺, i.i.d. loads on the complete graph are routable over direct and two-edge routes w.p. → 1
-- statement:
--   Consider the complete graph on $K$ nodes, every edge of capacity $C$. The offered load between each pair of nodes is a nonnegative real random variable distributed as $X$ (law $\mu$), and the offered loads of different pairs are independent. Let $P(K)$ be the probability that all offered loads can be carried over direct and two-edge routes, with no edge in the network required to carry more than its capacity (loads may be split arbitrarily over a pair's direct edge and its two-edge routes).
--
--   If $\mathbb E\,e^{\lambda X}<\infty$ for some $\lambda>0$, and
--   $$
--   2\,\mathbb E(X-C)^+<\mathbb E(C-X)^+ \tag{4.46}
--   $$
--   then
--   $$
--   P(K)\to 1\qquad (K\to\infty).
--   $$
--   The result extends Hajek's Theorem 4.40 on randomly coloured complete graphs to general load distributions: when the mean excess over capacity is less than half the mean spare capacity, alternative routing over two-edge paths absorbs every overload, with probability tending to one, in a large fully connected network.
--
--   **Formalization Note.** The exponential moment is integrability of $t\mapsto e^{\lambda t}$ under $\mu$; it makes $(X-C)^+$ integrable, so the Bochner integrals in (4.46) are the true expectations. (4.46) forces $\mathbb E(C-X)^+>0$ and hence $C>0$. The limit is taken along $K\in\mathbb N$; for $K\le 2$ there are no two-edge routes, which does not affect the limit.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 358, Theorem 4.45 (with (4.46))

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace KellyLossNetworks.Routing

/-- **Theorem 4.45.** Let the offered loads between the pairs of nodes of the complete graph on
`K` nodes be independent, each distributed as a nonnegative random variable `X` with law `μ`, and
let every edge have capacity `C`. If `𝔼 e^{θX} < ∞` for some `θ > 0` and
`2 𝔼(X - C)⁺ < 𝔼(C - X)⁺` (4.46), then the probability `P(K)` that all offered loads can be
carried over direct and two-edge routes, with no edge carrying more than `C`, tends to `1` as
`K → ∞`.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, p. 358, Theorem 4.45 (the printed "the P(K) → 1" is a misprint for "then").

**Formalization Note.** `(X - C)⁺` is integrable because `X` has an exponential moment, so the
Bochner integrals in (4.46) are the true expectations. `(4.46)` forces `𝔼(C - X)⁺ > 0`, hence
`C > 0`. -/
theorem theorem_4_45 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C : ℝ) (hmgf : ∃ θ : ℝ, 0 < θ ∧ Integrable (fun t => Real.exp (θ * t)) μ)
    (h446 : 2 * ∫ t, max (t - C) 0 ∂μ < ∫ t, max (C - t) 0 ∂μ) :
    Tendsto (fun K : ℕ => routingProb μ C K) atTop (𝓝 1) := by sorry

end KellyLossNetworks.Routing
