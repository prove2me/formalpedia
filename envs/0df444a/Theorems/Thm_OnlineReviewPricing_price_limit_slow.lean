-- Prove2me | Theorems.Thm_OnlineReviewPricing_price_limit_slow
-- name    : OnlineReviewPricing.price_limit_slow
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:37.007641+00:00
-- url     : https://prove2.me/theorems/3adac587-f88b-45f7-bb66-b10bab121110
-- title:
--   (EC.25), p.ec13 — the optimal price tends to $1+\exp(z_0^*)$ as $\gamma\to 0$
-- statement:
--   Fix $T>0$ and $t\in[0,T]$. For each $\gamma>0$ let $z(\gamma)$ be a root of (14), and let $p^*_\gamma$ be the price (13) at that root. Let $z_0^*$ satisfy
--
--   $$
--   z_0^*+\exp(z_0^*)=\mu_0-1 .
--   $$
--
--   Then
--
--   $$
--   p^*_\gamma(t)\to 1+\exp(z_0^*)\qquad\text{as }\gamma\to 0^+ .
--   $$
--
--   The limit does not depend on $t$: when learning is slow, the candidate price path is flat.
--
--   Differences from the source: none.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.25), p.ec13 (PDF 50)

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsRootOf14
import Definitions.Def_OnlineReviewPricing_candidatePrice

open Filter Topology

namespace OnlineReviewPricing

/-- For fixed `T > 0` and `t ∈ [0, T]`, and for any choice `z γ` of roots of (14), the price (13)
tends to `1 + exp z₀` as `γ → 0⁺`, where `z₀ + exp z₀ = μ₀ - 1`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.25), p.ec13). -/
theorem price_limit_slow (μ μ₀ T z₀ t : ℝ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (hz₀ : z₀ + Real.exp z₀ = μ₀ - 1) (z : ℝ → ℝ)
    (hz : ∀ γ, 0 < γ → IsRootOf14 μ μ₀ γ T (z γ)) :
    Tendsto (fun γ => candidatePrice μ μ₀ γ T (z γ) t) (𝓝[>] 0) (𝓝 (1 + Real.exp z₀)) := by sorry

end OnlineReviewPricing
