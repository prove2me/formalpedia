-- Prove2me | Theorems.Thm_KellyLossNetworks_Routing_mean_Z_lt_one
-- name    : KellyLossNetworks.Routing.mean_Z_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:23.855663+00:00
-- url     : https://prove2.me/theorems/7809acc6-1195-4704-b49c-e927c03ece30
-- title:
--   Proof of Thm 4.45, p. 359 — 𝔼Z = 2𝔼(X − C)⁺·m/(m² − ε) < 1 for ε small, by (4.46)
-- statement:
--   Let $X\ge 0$ be a random variable with law $\mu$ such that $(X-C)^+$ is integrable, and suppose (4.46):
--   $$
--   2\,\mathbb E(X-C)^+<\mathbb E(C-X)^+=:m .
--   $$
--   For $X_1,X_2$ independent copies of $X$ and $0<\varepsilon<m^2$ let
--   $$
--   Z=\frac{(X_1-C)^+(C-X_2)^+ + (X_2-C)^+(C-X_1)^+}{m^2-\varepsilon}.
--   $$
--   Then
--
--   1. for every $0<\varepsilon<m^2$, $\ \mathbb E\,Z=\dfrac{2\,\mathbb E(X-C)^+\, m}{m^2-\varepsilon}$; and
--   2. there is $\varepsilon_0\in(0,m^2]$ such that $\mathbb E\,Z<1$ for every $\varepsilon\in(0,\varepsilon_0)$.
--
--   This is the input to the upper-tail bound (4.49): an edge with excess capacity has, on average, less than its excess capacity reserved through it.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 359, §4.6, proof of Theorem 4.45, using (4.46) (p. 358)

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace KellyLossNetworks.Routing

/-- **The expectation of `Z` is less than 1 for `ε` small, by (4.46).** Let `X` be a nonnegative
random variable with law `μ` such that `(X - C)⁺` is integrable and
`2 𝔼(X - C)⁺ < 𝔼(C - X)⁺ =: m` (4.46). With `X₁, X₂` independent copies of `X` and
`Z = ((X₁ - C)⁺ (C - X₂)⁺ + (X₂ - C)⁺ (C - X₁)⁺) / (m² - ε)`:
for `0 < ε < m²`, `𝔼 Z = 2 𝔼(X - C)⁺ · m / (m² - ε)`; and there is `ε₀ ∈ (0, m²]` such that
`𝔼 Z < 1` for every `ε ∈ (0, ε₀)`.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, proof of Theorem 4.45, p. 359 ("But the expectation of Z is less than 1 for ε sufficiently
small, by (4.46)"). -/
theorem mean_Z_lt_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C : ℝ) (hint : Integrable (fun t => max (t - C) 0) μ)
    (h446 : 2 * excessMean μ C < spareMean μ C) :
    (∀ ε : ℝ, 0 < ε → ε < spareMean μ C ^ 2 →
      ∫ p, Zv μ C ε p ∂(μ.prod μ) =
        2 * excessMean μ C * spareMean μ C / (spareMean μ C ^ 2 - ε)) ∧
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ spareMean μ C ^ 2 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∫ p, Zv μ C ε p ∂(μ.prod μ) < 1 := by sorry

end KellyLossNetworks.Routing
