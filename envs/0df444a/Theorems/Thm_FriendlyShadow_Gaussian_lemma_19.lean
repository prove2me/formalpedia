-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_19
-- name    : FriendlyShadow.Gaussian.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:17:23.212994+00:00
-- url     : https://prove2.me/theorems/46c6db85-3ddf-405c-b557-26879ea048ef
-- title:
--   Lemma 19, p. 20 — mean 0 and n-th deviation at most rₙ ⇒ E[maxᵢ |θᵀxᵢ|] ≤ 2rₙ
-- statement:
--   Let $x_1,\dots,x_n$ be random vectors in $\mathbb R^d$ on a common probability space, not necessarily independent. Suppose each $x_i$ has a probability density with mean $0$ and $n$-th deviation at most $r$ (Definition 17). Then for every unit vector $\theta\in S^{d-1}$,
--   $$\mathbb E\Big[\max_{i\in[n]}|\theta^\mathsf{T}x_i|\Big]\le 2r .$$
--
--   The lemma converts the one-dimensional tail control encoded by the $n$-th deviation into a bound on the expected maximum of $n$ projections; it is the probabilistic input of the perimeter bound (Lemma 26).
--
--   **Formalization Note** The law of each $x_i$ is required to equal the measure with density $\mu_i$. The expectation is a lower Lebesgue integral of $\max_i|\theta^\mathsf{T}x_i|$ in $[0,\infty]$ (for $n=0$ the maximum is $0$).
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 19, p. 20

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Lemma 19 (Dadush–Huiberts, arXiv:1711.05667v4, p. 20). If `x₁, …, xₙ` are each distributed
with mean `0` and `n`-th deviation at most `r`, then for every unit vector `θ`,
`E[max_{i ∈ [n]} |θᵀxᵢ|] ≤ 2r`. No independence is assumed. -/
theorem lemma_19 {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, Measurable (x i)) (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hμ : ∀ i, IsDensity (μ i)) (hlaw : ∀ i, P.map (x i) = densityMeasure (μ i))
    (hmean : ∀ i, HasMean (μ i) 0) (r : ℝ) (hr : ∀ i, NthDeviationLE (μ i) 0 n r)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ = 1) :
    ∫⁻ ω, (⨆ i, ENNReal.ofReal |⟪θ, x i ω⟫|) ∂P ≤ ENNReal.ofReal (2 * r) := by sorry

end FriendlyShadow.Gaussian
