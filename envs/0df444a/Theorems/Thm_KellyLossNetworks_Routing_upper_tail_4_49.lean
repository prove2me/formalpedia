-- Prove2me | Theorems.Thm_KellyLossNetworks_Routing_upper_tail_4_49
-- name    : KellyLossNetworks.Routing.upper_tail_4_49
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:41.052001+00:00
-- url     : https://prove2.me/theorems/0cfc5249-262a-492c-ba53-5c802f4d4441
-- title:
--   (4.49), p. 359 — P₂ = ℙ{Σ (K − 2)⁻¹Zᵢ > 1} ≤ exp[−(K − 2)I₂] for some I₂ > 0
-- statement:
--   Let $X\ge 0$ be a random variable with law $\mu$ that has a moment generating function in a neighbourhood of the origin: $\mathbb E\,e^{\theta X}<\infty$ for some $\theta>0$. Let $m=\mathbb E(C-X)^+$, $0<\varepsilon<m^2$, and
--   $$
--   Z=\frac{(X_1-C)^+(C-X_2)^+ + (X_2-C)^+(C-X_1)^+}{m^2-\varepsilon}
--   $$
--   for independent copies $X_1,X_2$ of $X$, and suppose $\mathbb E\,Z<1$. There is a constant $I_2>0$, independent of $n$, such that for every $n\ge 1$ and independent copies $Z_1,\dots,Z_n$ of $Z$,
--   $$
--   P_2(n)=\mathbb P\Big\{\sum_{i=1}^{n} n^{-1}Z_i>1\Big\}\le e^{-nI_2}.
--   $$
--   With $n=K-2$ this bounds the probability that more capacity is reserved through one edge with excess capacity than it has spare. The statement includes the step "X (and hence Z) has a moment generating function in a neighborhood of the origin".
--
--   **Formalization Note.** The $Z_i$ are realised on $n$ independent copies of the pair $(X_1,X_2)$, i.e. under the $n$-fold product of $\mu\otimes\mu$; the rate $I_2$ is quantified before $n$. The exponential moment is stated as integrability of $t\mapsto e^{\theta t}$ under $\mu$.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 359, §4.6, proof of Theorem 4.45, (4.49)

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace KellyLossNetworks.Routing

/-- **(4.49)**: `P₂ ≤ exp[-(K - 2) I₂]` for some `I₂ > 0`. Let `X ≥ 0` have law `μ` with a
moment generating function in a neighbourhood of the origin (`𝔼 e^{θX} < ∞` for some `θ > 0`),
let `m = 𝔼(C - X)⁺`, `0 < ε < m²`, and suppose `𝔼 Z < 1` for
`Z = ((X₁ - C)⁺ (C - X₂)⁺ + (X₂ - C)⁺ (C - X₁)⁺) / (m² - ε)`. There is `I₂ > 0`, not depending
on `n`, such that for every `n ≥ 1` (`n = K - 2`), with `Z_1, …, Z_n` independent copies of `Z`,
`ℙ{∑_{i=1}^{n} n⁻¹ Z_i > 1} ≤ exp(-n I₂)`.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, proof of Theorem 4.45, p. 359, (4.49) ("Now X (and hence Z) has a moment generating
function in a neighborhood of the origin, and so [10]"). -/
theorem upper_tail_4_49 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C : ℝ) (hmgf : ∃ θ : ℝ, 0 < θ ∧ Integrable (fun t => Real.exp (θ * t)) μ)
    (ε : ℝ) (hε : 0 < ε) (hεm : ε < spareMean μ C ^ 2)
    (hZ : ∫ p, Zv μ C ε p ∂(μ.prod μ) < 1) :
    ∃ I₂ : ℝ, 0 < I₂ ∧ ∀ n : ℕ, 1 ≤ n →
      P2 μ C ε n ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * I₂))) := by sorry

end KellyLossNetworks.Routing
