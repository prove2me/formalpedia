-- Prove2me | Theorems.Thm_KellyLossNetworks_Routing_lower_tail_4_48
-- name    : KellyLossNetworks.Routing.lower_tail_4_48
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:31.357351+00:00
-- url     : https://prove2.me/theorems/0623b6db-a420-4338-9615-536ed98fa6c5
-- title:
--   (4.48), p. 359 — P₁ = ℙ{Σ (K − 2)⁻¹Yᵢ < 1} ≤ exp[−(K − 2)I₁] for some I₁ > 0
-- statement:
--   Let $X\ge 0$ be a random variable with law $\mu$, $m=\mathbb E(C-X)^+>0$ and $0<\varepsilon<m^2$, and let
--   $$
--   Y=\frac{(C-X_2)^+(C-X_3)^+}{m^2-\varepsilon}
--   $$
--   for independent copies $X_2,X_3$ of $X$. There is a constant $I_1>0$, independent of $n$, such that for every $n\ge 1$ and independent copies $Y_1,\dots,Y_n$ of $Y$,
--   $$
--   P_1(n)=\mathbb P\Big\{\sum_{i=1}^{n} n^{-1}Y_i<1\Big\}\le e^{-nI_1}.
--   $$
--   With $n=K-2$ this bounds the probability that the reservations made for one edge with excess flow fail to cope with its excess.
--
--   **Formalization Note.** The $Y_i$ are realised on $n$ independent copies of the pair $(X_2,X_3)$, i.e. under the $n$-fold product of $\mu\otimes\mu$; the rate $I_1$ is quantified before $n$.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 359, §4.6, proof of Theorem 4.45, (4.48)

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace KellyLossNetworks.Routing

/-- **(4.48)**: `P₁ ≤ exp[-(K - 2) I₁]` for some `I₁ > 0`. Let `X ≥ 0` have law `μ`, let
`m = 𝔼(C - X)⁺ > 0` and `0 < ε < m²`. There is `I₁ > 0`, not depending on `n`, such that for every
`n ≥ 1` (`n = K - 2`), with `Y_1, …, Y_n` independent copies of
`Y = (C - X₂)⁺ (C - X₃)⁺ / (m² - ε)`,
`ℙ{∑_{i=1}^{n} n⁻¹ Y_i < 1} ≤ exp(-n I₁)`.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, proof of Theorem 4.45, p. 359, (4.48). -/
theorem lower_tail_4_48 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C : ℝ) (hm : 0 < spareMean μ C) (ε : ℝ) (hε : 0 < ε) (hεm : ε < spareMean μ C ^ 2) :
    ∃ I₁ : ℝ, 0 < I₁ ∧ ∀ n : ℕ, 1 ≤ n →
      P1 μ C ε n ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * I₁))) := by sorry

end KellyLossNetworks.Routing
