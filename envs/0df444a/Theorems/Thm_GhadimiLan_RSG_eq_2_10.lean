-- Prove2me | Theorems.Thm_GhadimiLan_RSG_eq_2_10
-- name    : GhadimiLan.RSG.eq_2_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T15:11:02.056727+00:00
-- url     : https://prove2.me/theorems/ecf04ec8-36ae-4f55-8636-d7efb932bc4c
-- title:
--   (2.10), p. 7 — under A1, E[⟨∇f(x_k), δ_k⟩ | ξ_[k−1]] = 0
-- statement:
--   Let $f\in\mathcal C^{1,1}_L(\mathbb R^n)$, let $G$ be a Borel oracle, and let $x_1,x_2,\dots$ be an RSG run from $x_1$ satisfying Assumption A1 with respect to a filtration $(\mathcal F_k)$ (noise adapted; conditional unbiasedness $\mathbb E[G(x_k,\xi_k)\mid\mathcal F_{k-1}]=\nabla f(x_k)$; $\mathbb E\|G(x_k,\xi_k)-\nabla f(x_k)\|^2\le\sigma^2$). Write $\delta_k=G(x_k,\xi_k)-\nabla f(x_k)$. Then for every $k\ge1$ the random variable $\langle\nabla f(x_k),\delta_k\rangle$ is integrable and
--   $$\mathbb E\big[\langle\nabla f(x_k),\delta_k\rangle\,\big|\,\mathcal F_{k-1}\big]=0\quad\text{almost surely}.$$
--
--   The cross term in the summed descent inequality (2.9) therefore has mean zero, which is what lets the expectation of (2.9) be bounded without assuming the noise is independent.
--
--   **Formalization Note** In the paper the conditioning is on the history $\xi_{[k-1]}$; any filtration to which the noise is adapted is allowed here, the history filtration being one of them. No moment assumption on $\nabla f(x_k)$ is made: its integrability is part of the claim.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, Eq. (2.10), p. 7

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Eq. (2.10) (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, p. 7): under Assumption
A1 along an RSG run, for every `k ≥ 1` the scalar `⟨∇f(x_k), δ_k⟩` (with
`δ_k = G(x_k, ξ_k) − ∇f(x_k)`) is integrable and `E[⟨∇f(x_k), δ_k⟩ | ℱ_{k-1}] = 0` almost surely.
No integrability of `∇f(x_k)` is assumed: it is part of the claim. -/
theorem eq_2_10 {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ) μ ∧
    μ[fun ω => ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ | ℱ (k - 1)] =ᵐ[μ] 0 := by sorry

end GhadimiLan.RSG
