-- Prove2me | Theorems.Thm_GhadimiLan_RSG_eq_2_11
-- name    : GhadimiLan.RSG.eq_2_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:25.41261+00:00
-- url     : https://prove2.me/theorems/762bcd70-82b8-47c3-9e62-53e7ac9a5e47
-- title:
--   (2.11), p. 7 — Σ(γ_k − Lγ_k²/2)E‖∇f(x_k)‖² ≤ f(x_1) − f* + (Lσ²/2)Σγ_k²
-- statement:
--   Let $f\in\mathcal C^{1,1}_L(\mathbb R^n)$ with $L>0$ be bounded below with $f^*=\inf_x f(x)$. Run the RSG method from $x_1$ with a Borel oracle $G$ satisfying Assumption A1 (noise level $\sigma$), and stepsizes with $0<\gamma_k<2/L$ for $k=1,\dots,N$, where $N\ge1$. Then each $\|\nabla f(x_k)\|^2$, $k=1,\dots,N$, is integrable and
--   $$\sum_{k=1}^N\Big(\gamma_k-\frac L2\gamma_k^2\Big)\,\mathbb E\|\nabla f(x_k)\|^2\le f(x_1)-f^*+\frac{L\sigma^2}{2}\sum_{k=1}^N\gamma_k^2.$$
--
--   This is the averaged form of (2.9): together with the weighting identity for the random output index it yields Theorem 2.1 a).
--
--   **Formalization Note** The stepsize positivity $0<\gamma_k$ is added to the paper's $\gamma_k<2/L$, as everywhere in this mission. The expectation is over the noise.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, Eq. (2.11), p. 7

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Eq. (2.11) (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, p. 7): for
`f ∈ C^{1,1}_L(ℝⁿ)` (`L > 0`) bounded below with `f* = inf f`, stepsizes `0 < γ_k < 2/L`
(`k = 1, …, N`, `N ≥ 1`) and an RSG run under Assumption A1, each `‖∇f(x_k)‖²` is integrable
and `Σ_{k=1}^N (γ_k − (L/2)γ_k²) E‖∇f(x_k)‖² ≤ f(x_1) − f* + (Lσ²/2) Σ_{k=1}^N γ_k²`. -/
theorem eq_2_11 {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) :
    (∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ) ∧
    ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ ≤
      f x1 - fstar + L * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 := by sorry

end GhadimiLan.RSG
