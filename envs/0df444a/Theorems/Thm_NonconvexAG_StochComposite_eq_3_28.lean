-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_3_28
-- name    : NonconvexAG.StochComposite.eq_3_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:25:36.578591+00:00
-- url     : https://prove2.me/theorems/5499d635-bf5d-4a03-aa65-fa8c7036e5f6
-- title:
--   (3.28) — the mini-batch gradient Ḡ_k is conditionally unbiased with E‖Ḡ_k − ∇Ψ(x^md_k)‖² ≤ σ²/m_k
-- statement:
--   Consider the stochastic composite problem: $\Psi=f+h$ with $f$ having $L_f$-Lipschitz gradient, $h$ convex with $L_h$-Lipschitz gradient, $\mathcal X$ convex with domain $K$ and prox map $\mathcal P$. Run Algorithm 4 with mini-batch gradients $\bar G_k=\frac1{m_k}\sum_{i=1}^{m_k}G(x^{md}_k,\xi_{k,i})$, the oracle $G$ being jointly measurable. Number the oracle calls consecutively and let $\mathcal F_s$ be a filtration to which the call samples are adapted. Suppose Assumption 1 holds for every call $s\ge1$ in conditional form: the output at the call's query point $q_s$ is integrable with $\mathbb E[G(q_s,\xi_s)\mid\mathcal F_{s-1}]=\nabla\Psi(q_s)$ and $\mathbb E\|G(q_s,\xi_s)-\nabla\Psi(q_s)\|^2\le\sigma^2$. Then for every $k\ge1$, with $S_{k-1}=m_1+\dots+m_{k-1}$,
--   $$\mathbb E\big[\bar G_k\,\big|\,\mathcal F_{S_{k-1}}\big]=\nabla\Psi(x^{md}_k)\ \text{a.s.},\qquad \mathbb E\big[\|\bar G_k-\nabla\Psi(x^{md}_k)\|^2\big]\le\frac{\sigma^2}{m_k},$$
--   and $\bar G_k$ and $\|\bar G_k-\nabla\Psi(x^{md}_k)\|^2$ are integrable.
--
--   Averaging $m_k$ oracle outputs divides the variance of the gradient estimate by $m_k$; this is what lets the batch sizes control the noise terms in Theorem 4.
--
--   **Formalization Note** The paper writes the first identity as $\mathbb E[\bar G_k]=\nabla\Psi(x^{md}_k)$; since $x^{md}_k$ is random, it is stated conditionally on the samples drawn before iteration $k$. The paper states Assumption 1 unconditionally ("for any $x$ and $k$") and cites [13, p. 11] for the variance bound; that bound needs the cross terms between calls of one batch to vanish, which is what the conditional form `GhadimiLan.RSG.AssumptionA1` along the query points (`querySeq`) provides. It holds in the paper's i.i.d. setting. The bound is a conclusion, not a hypothesis.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 3, Assumption 1; p. 21, (3.25) and (3.28)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- (3.28), p. 21 (outer ends of both lines), for Algorithm 4: under Assumption 1 imposed on the
oracle calls in their order (conditional form, along the query points), for every `k ≥ 1` the
mini-batch gradient `Ḡₖ` (3.25) is integrable and conditionally unbiased given the first
`S_{k−1} = m₁ + ⋯ + m_{k−1}` oracle calls, `E[Ḡₖ | ℱ_{S_{k−1}}] = ∇Ψ(x^md_k)` a.s., and
`E‖Ḡₖ − ∇Ψ(x^md_k)‖² ≤ σ²/mₖ` (with `‖Ḡₖ − ∇Ψ(x^md_k)‖²` integrable). -/
theorem eq_3_28 {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ gΨ G ξ (querySeq G P α β lam m x0 ξ) σ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let Gb : ℕ → Ω → E n := Gbar G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ k, 1 ≤ k →
      Integrable (Gb k) μ ∧
      μ[Gb k | ℱ (batchEnd m (k - 1))] =ᵐ[μ] (fun ω => gΨ (xmd k ω)) ∧
      Integrable (fun ω => ‖δ k ω‖ ^ 2) μ ∧
      ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ≤ σ ^ 2 / (m k : ℝ) := by sorry

end NonconvexAG.StochComposite
