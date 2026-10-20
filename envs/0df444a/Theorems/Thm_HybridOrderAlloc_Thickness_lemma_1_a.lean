-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_lemma_1_a
-- name    : HybridOrderAlloc.Thickness.lemma_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:04.802364+00:00
-- url     : https://prove2.me/theorems/1baa84cb-a7ec-4441-98ba-3ccf6e38dd01
-- title:
--   Lemma 1(a), p. 35 — the envelope formulas (13) for ∂₁V_t and ∂₂V_t
-- statement:
--   Consider the order-allocation dynamic program of He & Goh with value functions $V_t$ given by (5), and the right partial derivatives $\partial_1V_t$, $\partial_2V_t$.
--
--   Let $t\in\{1,\dots,T\}$ and $(M,D)\in\mathbb R^2_{++}$. Let $y^*\in[0,D]$ be an optimal decision for problem (5) in period $t$, and let $\lambda^*\ge0$ be an optimal dual variable of the constraint $y\le D$: $\lambda^*(D-y^*)=0$ and $y^*$ maximizes the objective of (5) minus $\lambda^*(y-D)$ over $y\ge0$. Write $M'=(\rho+\delta R\beta)M+\delta Ry^*$ and $D'=\eta D+\theta M+\epsilon$. Then the right partial derivatives of $V_t$ at $(M,D)$ exist and
--   $$\partial_1V_t(M,D)=p\tilde\mu+\frac{pR}{M^2}(y^*)^2+\gamma\,\mathbb E\big[(\rho+\delta R\beta)\,\partial_1V_{t+1}(M',D')\big]+\gamma\,\mathbb E\big[\theta\,\partial_2V_{t+1}(M',D')\big],$$
--   $$\partial_2V_t(M,D)=\lambda^*+r+\gamma\eta\,\mathbb E\big[\partial_2V_{t+1}(M',D')\big].\qquad(13)$$
--
--   These envelope formulas express the marginal values of thickness and of firm demand recursively, and drive the sign analysis behind Theorem 1.
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 35, Lemma 1(a), (13)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

open MeasureTheory

/-- **Lemma 1(a)**, p. 35, (13): for every period `t ∈ {1, …, T}` and `(M, D) ∈ ℝ²₊₊`, if `y*` is an
optimal decision of (5) and `λ* ≥ 0` an optimal dual variable of the constraint `y ≤ D` with
`λ*(D − y*) = 0`, then the right partial derivatives of `V_t` exist and are
`∂₁V_t = pµ̃ + (pR/M²)(y*)² + γE[(ρ + δRβ)∂₁V_{t+1}(M', D')] + γE[θ ∂₂V_{t+1}(M', D')]` and
`∂₂V_t = λ* + r + γηE[∂₂V_{t+1}(M', D')]`, where `M' = (ρ + δRβ)M + δRy*`, `D' = ηD + θM + ϵ`.
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. -/
theorem lemma_1_a {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    ∀ t : ℕ, 1 ≤ t → t ≤ S.T → ∀ M D : ℝ, 0 < M → 0 < D → ∀ ys lam : ℝ,
      ys ∈ Set.Icc 0 D → IsMaxOn (S.stage (S.V (t + 1)) M D) (Set.Icc 0 D) ys →
      0 ≤ lam → lam * (D - ys) = 0 →
      IsMaxOn (fun y => S.stage (S.V (t + 1)) M D y - lam * (y - D)) (Set.Ici 0) ys →
      HasDerivWithinAt (fun M' => S.V t M' D)
          (S.p * S.muTilde + S.p * S.R / M ^ 2 * ys ^ 2
            + S.gam * (∫ ω, (S.rho + S.delta * S.R * S.beta ω) *
                S.d1V (t + 1) ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * ys)
                  (S.eta * D + S.theta ω * M + S.eps ω) ∂S.P)
            + S.gam * (∫ ω, S.theta ω *
                S.d2V (t + 1) ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * ys)
                  (S.eta * D + S.theta ω * M + S.eps ω) ∂S.P))
          (Set.Ioi M) M ∧
        HasDerivWithinAt (fun D' => S.V t M D')
          (lam + S.r + S.gam * S.eta * (∫ ω,
                S.d2V (t + 1) ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * ys)
                  (S.eta * D + S.theta ω * M + S.eps ω) ∂S.P))
          (Set.Ioi D) D := by sorry

end HybridOrderAlloc.Thickness
