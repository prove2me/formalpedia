-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_sf_objective_eq
-- name    : MixFlex.RiskNeutral.sf_objective_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:52:32.19337+00:00
-- url     : https://prove2.me/theorems/c0e078b9-7763-420c-9e8a-2385541be42d
-- title:
--   (9) — the risk-neutral SF objective in closed form
-- statement:
--   In the SF network of the mission's model, let $S=\tilde X_{N+1}=\tilde X_1+\dots+\tilde X_N$ be total demand, $c_{N+1}$ the flexible resource's marginal total cost and $K=K_{N+1}\ge 0$ the flexible investment. Then
--   $$
--   V^{SF}_{RN}(K)=-(\lambda+(1-\lambda)\theta)\,c_{N+1}K+\theta p\Big(\mathbb E\big[S\,\mathbf 1\{S\le K\}\big]+K\big(1-\mathbb P(S\le K)\big)\Big).
--   $$
--   This is equation (9) of the paper: the SF problem is a single-product newsvendor problem with Bernoulli investment failures, whose expected cost is the committed cost plus the delivered cost weighted by $\theta$, and whose expected revenue is $\theta p\,\mathbb E[\min\{S,K\}]$.
--
--   **Formalization Note** The paper writes $\int_0^{K}x f_{X_{N+1}}(x)\,dx$; since no density is assumed, it is rendered as $\mathbb E[S\,\mathbf 1\{S\le K\}]$, which equals it for a nonnegative $S$ with a density.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 41, §3.1, (9)

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- (9), p. 41: the risk-neutral SF objective in closed form. The density integral
`∫_0^K x f(x) dx` is written as `E[S · 1{S ≤ K}]` with `S = X_1 + ⋯ + X_N`. -/
theorem sf_objective_eq (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) (hS : Setting P μ X Y)
    (cF K : ℝ) (hK : 0 ≤ K) :
    vSF P μ X Y cF K =
      -(P.lam + (1 - P.lam) * P.theta) * cF * K
        + P.theta * P.p * ((∫ ω, (∑ n, X ω n) * (if ∑ n, X ω n ≤ K then 1 else 0) ∂μ)
          + K * (1 - μ.real {ω | ∑ n, X ω n ≤ K})) := by sorry

end MixFlex.RiskNeutral
