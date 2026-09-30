-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_premium_nonneg_iff_expectedShortfall
-- name    : MixFlex.RiskNeutral.premium_nonneg_iff_expectedShortfall
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:55:41.844143+00:00
-- url     : https://prove2.me/theorems/89294abb-d7f6-470e-b310-a5bdcf5f2570
-- title:
--   (A-1) in expected-shortfall form — SF is preferred at equal cost iff ES is subadditive on the demands
-- statement:
--   In the mission's model, let
--   $$
--   \alpha=1-\frac{(\lambda+(1-\lambda)\theta)\,c}{\theta p}
--   $$
--   and suppose $0<\alpha<1$. Then SF is weakly preferred to SD at $c_{N+1}=c$ (that is, $V^{SF,*}_{RN}\ge V^{SD,*}_{RN}$) if and only if
--   $$
--   \alpha\Big(\sum_{n=1}^N ES_\alpha(\tilde X_n)-ES_\alpha\Big(\sum_{n=1}^N\tilde X_n\Big)\Big)\ge 0,
--   $$
--   where $ES_\alpha$ is the Acerbi–Tasche $\alpha$-expected shortfall.
--
--   This is the reformulation of (A-1) in the proof of Proposition 1(i): the optimal SF and SD values are $-\theta p\,\alpha$ times the expected shortfalls of total demand and of the individual demands, so comparing the networks at equal cost reduces to a property of expected shortfall.
--
--   **Formalization Note** The condition $\alpha\in(0,1)$ is the page's own note; it forces $\theta>0$. The statement is for general nonnegative integrable demand, using Acerbi–Tasche's general expected-shortfall formula; for continuous demand it is the page's identity $\int_0^{F^{-1}[\alpha]}xf(x)\,dx=-\alpha ES_\alpha(X)$.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 52, Appendix A, proof of PROPOSITION 1(i), (A-1) and the display following it

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- (A-1) in expected-shortfall form (Appendix A, proof of Proposition 1(i), p. 52): with
`α = 1 − (λ + (1 − λ)θ) c / (θ p) ∈ (0, 1)`, SF is weakly preferred at `c_{N+1} = c` iff
`α (Σ_n ES_α(X_n) − ES_α(Σ_n X_n)) ≥ 0`. -/
theorem premium_nonneg_iff_expectedShortfall (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) (α : ℝ)
    (hα : α = 1 - (P.lam + (1 - P.lam) * P.theta) * P.c / (P.theta * P.p))
    (hα0 : 0 < α) (hα1 : α < 1) :
    SFPreferred P μ X Y P.c ↔
      0 ≤ α * ((∑ n, expectedShortfall μ (fun ω => X ω n) α)
        - expectedShortfall μ (fun ω => ∑ n, X ω n) α) := by sorry

end MixFlex.RiskNeutral
