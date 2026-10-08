-- Prove2me | Theorems.Thm_KellyLossNetworks_Routing_mean_Y_gt_one
-- name    : KellyLossNetworks.Routing.mean_Y_gt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:14.532036+00:00
-- url     : https://prove2.me/theorems/92b6c69d-15e2-4868-a6cf-166c326b9ef7
-- title:
--   Proof of Thm 4.45, p. 359 — 𝔼Y = m²/(m² − ε) > 1
-- statement:
--   Let $X\ge 0$ be a random variable with law $\mu$, let $C\in\mathbb R$, and suppose $m=\mathbb E(C-X)^+>0$. Let $0<\varepsilon<m^2$ and let $X_2,X_3$ be independent copies of $X$. Then
--   $$
--   Y=\frac{(C-X_2)^+(C-X_3)^+}{m^2-\varepsilon}
--   $$
--   has expectation
--   $$
--   \mathbb E\,Y=\frac{m^2}{m^2-\varepsilon}>1 .
--   $$
--   This is the input to the lower-tail bound (4.48): an excess edge receives, through its $K-2$ triangles, a reservation whose average multiplier exceeds $1$.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 359, §4.6, proof of Theorem 4.45

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace KellyLossNetworks.Routing

/-- **The expectation of `Y` is greater than 1.** Let `X` be a nonnegative random variable with
law `μ`, and `m = 𝔼(C - X)⁺ > 0`. For `0 < ε < m²`, with `X₂, X₃` independent copies of `X`,
`𝔼 Y = m² / (m² - ε) > 1` where `Y = (C - X₂)⁺ (C - X₃)⁺ / (m² - ε)`.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, proof of Theorem 4.45, p. 359 ("But the expectation of Y is greater than 1"). -/
theorem mean_Y_gt_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C : ℝ) (hm : 0 < spareMean μ C) (ε : ℝ) (hε : 0 < ε) (hεm : ε < spareMean μ C ^ 2) :
    ∫ p, Yv μ C ε p ∂(μ.prod μ) = spareMean μ C ^ 2 / (spareMean μ C ^ 2 - ε) ∧
    1 < ∫ p, Yv μ C ε p ∂(μ.prod μ) := by sorry

end KellyLossNetworks.Routing
