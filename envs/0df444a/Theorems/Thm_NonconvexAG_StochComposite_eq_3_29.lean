-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_3_29
-- name    : NonconvexAG.StochComposite.eq_3_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:29.067543+00:00
-- url     : https://prove2.me/theorems/fc141a88-d6d0-4a90-a2dc-72d279668bd9
-- title:
--   (3.29) — E‖𝒢(x^md_k, ∇Ψ(x^md_k), β_k) − 𝒢(x^md_k, Ḡ_k, β_k)‖² ≤ E‖Ḡ_k − ∇Ψ(x^md_k)‖² ≤ σ²/m_k
-- statement:
--   In the setting of (3.28) (Algorithm 4 on the stochastic composite problem, with Assumption 1 in conditional form along the oracle's query points), for every $k\ge1$ the exact and the stochastic gradient mappings at $x^{md}_k$ satisfy
--   $$\mathbb E\Big[\big\|\mathcal G(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k)-\mathcal G(x^{md}_k,\bar G_k,\beta_k)\big\|^2\Big]\le\mathbb E\big[\|\bar G_k-\nabla\Psi(x^{md}_k)\|^2\big]\le\frac{\sigma^2}{m_k},$$
--   and the quantity on the left is integrable.
--
--   Since $\nabla\Psi(x^{md}_k)$ is not available, the method can only compute $\mathcal G(x^{md}_k,\bar G_k,\beta_k)$; this estimate bounds the price of that substitution.
--
--   **Formalization Note** Same model as (3.28): `GhadimiLan.RSG.AssumptionA1` along `querySeq`, a jointly measurable oracle, and the prox map on the domain $K$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 21, (3.29)

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

/-- (3.29), p. 21, for Algorithm 4: under Assumption 1 (conditional form, along the query points),
for every `k ≥ 1`, `‖𝒢(x^md_k, ∇Ψ(x^md_k), βₖ) − 𝒢(x^md_k, Ḡₖ, βₖ)‖²` is integrable and
`E‖𝒢(x^md_k, ∇Ψ(x^md_k), βₖ) − 𝒢(x^md_k, Ḡₖ, βₖ)‖² ≤ E‖Ḡₖ − ∇Ψ(x^md_k)‖² ≤ σ²/mₖ`. -/
theorem eq_3_29 {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
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
      Integrable (fun ω => ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k) -
        gradMap P (xmd k ω) (Gb k ω) (β k)‖ ^ 2) μ ∧
      ∫ ω, ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k) -
          gradMap P (xmd k ω) (Gb k ω) (β k)‖ ^ 2 ∂μ ≤ ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ∧
      ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ≤ σ ^ 2 / (m k : ℝ) := by sorry

end NonconvexAG.StochComposite
