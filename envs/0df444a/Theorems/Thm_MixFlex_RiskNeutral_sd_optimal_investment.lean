-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_sd_optimal_investment
-- name    : MixFlex.RiskNeutral.sd_optimal_investment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:54:32.451645+00:00
-- url     : https://prove2.me/theorems/398c4b17-1baf-409b-9c3d-c2d997088567
-- title:
--   (12)–(13) — the SD problem decomposes into N single-product newsvendor problems
-- statement:
--   In the SD network of the mission's model, suppose $\theta>0$ and let $K^*=(K^*_1,\dots,K^*_N)\ge 0$ satisfy, for every product $n$,
--   $$
--   F_{X_n}(K^*_n)=1-\frac{(\lambda+(1-\lambda)\theta)\,c}{\theta p}.
--   $$
--   Then $K^*$ maximizes $V^{SD}_{RN}$ over all $K\ge 0$, and the optimal SD value is
--   $$
--   V^{SD,*}_{RN}=V^{SD}_{RN}(K^*)=\theta p\sum_{n=1}^N\mathbb E\big[\tilde X_n\,\mathbf 1\{\tilde X_n\le K^*_n\}\big].
--   $$
--   These are equations (12)–(13): the SD investment problem splits into $N$ independent single-product problems, each solved by the same critical fractile.
--
--   **Formalization Note** As in (10)–(11), $F^{-1}_{X_n}$ is replaced by the hypothesis $F_{X_n}(K^*_n)=$ fractile, and $\int_0^{K^*_n}x f_{X_n}(x)\,dx$ by $\mathbb E[\tilde X_n\mathbf 1\{\tilde X_n\le K^*_n\}]$. $\theta>0$ is needed for the fractile to be defined.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 42, §3.1, (12)–(13)

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- (12)–(13), p. 42: the SD problem decomposes into `N` single-product problems; any `K* ≥ 0`
with `F_{X_n}(K*_n) = 1 − (λ + (1 − λ)θ) c / (θ p)` for every `n` is an optimal SD investment,
and the optimal SD value is `θ p Σ_n E[X_n · 1{X_n ≤ K*_n}]`. -/
theorem sd_optimal_investment (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) (htheta : 0 < P.theta) (Kstar : Fin N → ℝ) (hK : ∀ n, 0 ≤ Kstar n)
    (hq : ∀ n, μ.real {ω | X ω n ≤ Kstar n}
      = 1 - (P.lam + (1 - P.lam) * P.theta) * P.c / (P.theta * P.p)) :
    (∀ K : Fin N → ℝ, (∀ n, 0 ≤ K n) → vSD P μ X Y K ≤ vSD P μ X Y Kstar) ∧
    vSD P μ X Y Kstar
      = P.theta * P.p * ∑ n, ∫ ω, X ω n * (if X ω n ≤ Kstar n then 1 else 0) ∂μ := by sorry

end MixFlex.RiskNeutral
