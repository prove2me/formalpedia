-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_sf_optimal_investment
-- name    : MixFlex.RiskNeutral.sf_optimal_investment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:53:17.018993+00:00
-- url     : https://prove2.me/theorems/289b4d23-265b-4bd5-b628-1f43d968d512
-- title:
--   (10)–(11) — the optimal flexible investment is the critical fractile of total demand
-- statement:
--   In the SF network of the mission's model, suppose $\theta>0$, let $S=\tilde X_1+\dots+\tilde X_N$ be total demand with distribution function $F_S$, and let $K^*\ge 0$ satisfy the critical-fractile condition
--   $$
--   F_S(K^*)=1-\frac{(\lambda+(1-\lambda)\theta)\,c_{N+1}}{\theta p}.
--   $$
--   Then $K^*$ maximizes $V^{SF}_{RN}$ over all $K\ge 0$, and the optimal SF value is
--   $$
--   V^{SF,*}_{RN}=V^{SF}_{RN}(K^*)=\theta p\,\mathbb E\big[S\,\mathbf 1\{S\le K^*\}\big].
--   $$
--   These are equations (10)–(11): the optimal flexible investment is a quantile of total demand, and its value is a partial expectation of total demand.
--
--   **Formalization Note** Mathlib has no quantile function $F^{-1}$; (10) is stated as "any $K^*\ge 0$ with $F_S(K^*)$ equal to the fractile is optimal". For a demand whose distribution function skips the fractile no such $K^*$ exists and the statement is vacuous for that instance. $\theta>0$ is needed for the fractile to be defined. $\int_0^{K^*}xf(x)\,dx$ is rendered as $\mathbb E[S\mathbf 1\{S\le K^*\}]$.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 42, §3.1, (10)–(11)

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- (10)–(11), p. 42: any `K* ≥ 0` at which the distribution function of total demand equals the
critical fractile `1 − (λ + (1 − λ)θ) c_{N+1} / (θ p)` is an optimal SF investment, and the optimal
SF value is `θ p E[S · 1{S ≤ K*}]`. -/
theorem sf_optimal_investment (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) (htheta : 0 < P.theta) (cF Kstar : ℝ) (hK : 0 ≤ Kstar)
    (hq : μ.real {ω | ∑ n, X ω n ≤ Kstar}
      = 1 - (P.lam + (1 - P.lam) * P.theta) * cF / (P.theta * P.p)) :
    (∀ K : ℝ, 0 ≤ K → vSF P μ X Y cF K ≤ vSF P μ X Y cF Kstar) ∧
    vSF P μ X Y cF Kstar
      = P.theta * P.p * ∫ ω, (∑ n, X ω n) * (if ∑ n, X ω n ≤ Kstar then 1 else 0) ∂μ := by sorry

end MixFlex.RiskNeutral
