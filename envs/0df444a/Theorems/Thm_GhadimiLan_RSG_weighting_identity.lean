-- Prove2me | Theorems.Thm_GhadimiLan_RSG_weighting_identity
-- name    : GhadimiLan.RSG.weighting_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:47.87321+00:00
-- url     : https://prove2.me/theorems/bcad984f-1fbb-46b6-ae71-ff89eb046615
-- title:
--   Proof of Theorem 2.1, p. 7 — E‖∇f(x_R)‖² = Σ(2γ_k − Lγ_k²)E‖∇f(x_k)‖² / Σ(2γ_k − Lγ_k²)
-- statement:
--   Let $f\in\mathcal C^{1,1}_L(\mathbb R^n)$ with $L>0$, let $G$ be a Borel oracle, let the noise variables $\xi_k$ be measurable, and let $x_1,x_2,\dots$ be the RSG run from $x_1$ with stepsizes $0<\gamma_k<2/L$ for $k=1,\dots,N$, $N\ge1$. Let the output index $R$ take values in $\{1,\dots,N\}$ with $\Pr\{R=k\}=P_R(k)=(2\gamma_k-L\gamma_k^2)/\sum_{j=1}^N(2\gamma_j-L\gamma_j^2)$, and let $R$ be independent of the noise sequence $(\xi_k)_{k\ge1}$. If $\|\nabla f(x_k)\|^2$ is integrable for every $k=1,\dots,N$, then $\|\nabla f(x_R)\|^2$ is integrable and
--   $$\mathbb E\|\nabla f(x_R)\|^2=\frac{\sum_{k=1}^N\big(2\gamma_k-L\gamma_k^2\big)\,\mathbb E\|\nabla f(x_k)\|^2}{\sum_{k=1}^N\big(2\gamma_k-L\gamma_k^2\big)}.$$
--
--   This is the step where the randomized output enters: the expected squared gradient at the random iterate is the $P_R$-weighted average of the expected squared gradients along the trajectory.
--
--   **Formalization Note** The independence of $R$ from the noise is implicit in the paper (Step 0 draws $R$ before any oracle call, and the expectation is "with respect to $R$ and $\xi_{[N]}$"); it is stated explicitly, and without it the identity fails. The left side is the integral of $\|\nabla f(x_{R(\omega)}(\omega))\|^2$, not the weighted sum.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, p. 7, display after "Dividing both sides"

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- The weighting identity in the proof of Theorem 2.1 (Ghadimi & Lan, arXiv:1309.5549v1, p. 7,
display after "Dividing both sides"): if the output index `R` has the mass function (2.3) on
`{1, …, N}` and is independent of the noise sequence `(ξ_k)`, and each `‖∇f(x_k)‖²`
(`k = 1, …, N`) is integrable, then `‖∇f(x_R)‖²` is integrable and
`E‖∇f(x_R)‖² = Σ_{k=1}^N (2γ_k − Lγ_k²) E‖∇f(x_k)‖² / Σ_{k=1}^N (2γ_k − Lγ_k²)`. -/
theorem weighting_identity {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (hξ : ∀ k, Measurable (ξ k))
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (R : Ω → ℕ) (hR : IsRandomOutputIndex μ R L γ N)
    (hRind : IndepFun R (fun ω k => ξ k ω) μ)
    (hint : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ) :
    Integrable (fun ω => ‖g (x (R ω) ω)‖ ^ 2) μ ∧
    ∫ ω, ‖g (x (R ω) ω)‖ ^ 2 ∂μ =
      (∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ) /
        ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by sorry

end GhadimiLan.RSG
