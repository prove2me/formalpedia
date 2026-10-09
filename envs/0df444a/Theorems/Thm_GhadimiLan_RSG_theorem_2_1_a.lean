-- Prove2me | Theorems.Thm_GhadimiLan_RSG_theorem_2_1_a
-- name    : GhadimiLan.RSG.theorem_2_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T15:11:00.632765+00:00
-- url     : https://prove2.me/theorems/4fda58f8-54d7-4e67-8a1c-41de845306e2
-- title:
--   Theorem 2.1 a), p. 6 — for 0 < γ_k < 2/L and P_R of (2.3), (1/L)E‖∇f(x_R)‖² ≤ (D_f² + σ²Σγ_k²)/Σ(2γ_k − Lγ_k²)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable with $L$-Lipschitz gradient ($L>0$), bounded below, with $f^*=\inf_{x\in\mathbb R^n}f(x)$. Let $G$ be a Borel stochastic first-order oracle and run the randomized stochastic gradient (RSG) method
--   $$x_{k+1}=x_k-\gamma_k\,G(x_k,\xi_k),\qquad k\ge1,$$
--   from $x_1$, under Assumption A1 with noise level $\sigma\ge0$: conditionally on the past, $G(x_k,\xi_k)$ is an unbiased estimate of $\nabla f(x_k)$, and $\mathbb E\|G(x_k,\xi_k)-\nabla f(x_k)\|^2\le\sigma^2$. Let $N\ge1$, let the stepsizes satisfy $0<\gamma_k<2/L$ for $k=1,\dots,N$, and let the output index $R$, independent of the noise, have the mass function
--   $$P_R(k)=\Pr\{R=k\}=\frac{2\gamma_k-L\gamma_k^2}{\sum_{j=1}^N(2\gamma_j-L\gamma_j^2)},\qquad k=1,\dots,N.$$
--   Then $\|\nabla f(x_R)\|^2$ is integrable and
--   $$\frac1L\,\mathbb E\big[\|\nabla f(x_R)\|^2\big]\le\frac{D_f^2+\sigma^2\sum_{k=1}^N\gamma_k^2}{\sum_{k=1}^N(2\gamma_k-L\gamma_k^2)},\qquad D_f=\Big[\frac{2(f(x_1)-f^*)}{L}\Big]^{1/2},$$
--   where the expectation is taken with respect to both $R$ and the noise $\xi_1,\dots,\xi_N$.
--
--   This is the basic complexity bound for stochastic gradient descent on smooth nonconvex objectives: with the stepsize policy of Corollary 2.2 it gives $\mathbb E\|\nabla f(x_R)\|^2=O(1/N+\sigma/\sqrt N)$, and it is the result on which the two-phase RSG method and the zeroth-order RSGF method of the same paper are built.
--
--   **Formalization Note** $f\in\mathcal C^{1,1}_L$ is the published predicate `IsBetaSmooth f g L` with $g=\nabla f$; $f^*$ is the greatest lower bound of the range of $f$. Three hypotheses implicit in the paper are explicit: $L>0$ (the paper divides by $L$), $\gamma_k>0$ (otherwise $P_R$ is not a probability mass function), and the independence of $R$ from the whole noise sequence (Step 0 draws $R$ first). Assumption A1 is stated in the conditional form the proof uses, with respect to any filtration to which the noise is adapted; the noise need not be independent. Integrability of $\|\nabla f(x_R)\|^2$ is part of the conclusion, since Lean's integral of a non-integrable function is $0$.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Theorem 2.1 a), Eqs. (2.3)–(2.5), p. 6

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Theorem 2.1 a), Eq. (2.4) (Ghadimi & Lan, arXiv:1309.5549v1, p. 6). Let `f ∈ C^{1,1}_L(ℝⁿ)`
(`L > 0`) have gradient map `g = ∇f` and be bounded below with `f* = inf f`. Run the RSG method
(2.2) from `x1` with a Borel oracle `G` satisfying Assumption A1 (noise level `σ`), stepsizes
`0 < γ_k < 2/L` for `k = 1, …, N` (`N ≥ 1`), and an output index `R` with mass function (2.3)
drawn independently of the noise. Then `‖∇f(x_R)‖²` is integrable and
`(1/L) E‖∇f(x_R)‖² ≤ (D_f² + σ² Σ_{k=1}^N γ_k²) / Σ_{k=1}^N (2γ_k − Lγ_k²)`, where
`D_f = [2(f(x_1) − f*)/L]^{1/2}` and the expectation is over both `R` and the noise. -/
theorem theorem_2_1_a {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ)
    (R : Ω → ℕ) (hR : IsRandomOutputIndex μ R L γ N)
    (hRind : IndepFun R (fun ω k => ξ k ω) μ) :
    Integrable (fun ω => ‖g (x (R ω) ω)‖ ^ 2) μ ∧
    1 / L * ∫ ω, ‖g (x (R ω) ω)‖ ^ 2 ∂μ ≤
      (Df f x1 fstar L ^ 2 + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) /
        ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by sorry

end GhadimiLan.RSG
