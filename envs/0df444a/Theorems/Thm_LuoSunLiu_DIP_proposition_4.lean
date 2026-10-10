-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_proposition_4
-- name    : LuoSunLiu.DIP.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:55.832992+00:00
-- url     : https://prove2.me/theorems/5fd7e70a-dc16-403c-92c2-9122a51bce94
-- title:
--   Proposition 4, p. 23 — w.p. ≥ 1 − δ, R_{T₀,1} ≤ 2√(2dT₀β*_{T₀} log((dλ + T₀p²_max)/(dλ))) + 4p_max L‖θ̂ − θ₀‖₁T₀ + 2dp_max
-- statement:
--   Let $F$ be $L$-Lipschitz (Assumption 1) and let the standing assumptions of the pricing model hold. Fix an estimate $\hat\theta$ and $d \ge 1$ with $p_{\max} + 2\|\hat\theta\|_1 < d\,p_{\max}$, and let $\lambda > 0$, $\delta \in (0, 1)$ and $T_0 \ge 1$. Suppose that on every sample path the prices of periods $1, \dots, T_0$ are a run of Inner Algorithm B (Algorithm 3) with estimate $\hat\theta$ and $\beta_t = \beta^*_t$. Then with probability at least $1 - \delta$ the discrete-part regret satisfies
--   $$R_{T_0,1} \le 2\sqrt{2dT_0\beta^*_{T_0}\log\frac{d\lambda + T_0p_{\max}^2}{d\lambda}} + 4p_{\max}L\|\hat\theta - \theta_0\|_1T_0 + 2dp_{\max}.$$
--   Here $R_{T_0,1} = \sum_{t=1}^{T_0}\bigl(\tilde p^*_t(1 - F(\tilde p^*_t - x_t^\top\theta_0)) - p_t(1 - F(p_t - x_t^\top\theta_0))\bigr)$ and $\tilde p^*_t$ is the best price in the candidate set $\mathcal S_t$.
--
--   This is the regret against the best grid price; Proposition 3 adds the discretization error.
--
--   **Formalization Note** The hypothesis $p_{\max} + 2\|\hat\theta\|_1 < d\,p_{\max}$ (grid step below $p_{\max}$) is added: it makes every candidate set $\mathcal S_t$ nonempty, without which Algorithm 3 cannot post a price. "With probability at least $1-\delta$" is the inner-measure reading (a measurable event of probability at least $1-\delta$). Covariates may be adaptive or adversarial, and $\mathcal G$ is any filtration as in the model.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 23, Proposition 4; proof pp. 46–49

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB

open MeasureTheory ProbabilityTheory NNReal

namespace LuoSunLiu.DIP

/-- Proposition 4 (Luo, Sun and Liu, arXiv:2109.07340v2, p. 23; proof pp. 46–49). Under
Assumption 1 (`F` is `L`-Lipschitz), for a single episode with fixed estimate `θ̂`, `d` grid
points with `p_max + 2‖θ̂‖₁ < d p_max`, `λ > 0` and `δ ∈ (0, 1)`, if on every sample path the
prices up to `T₀` are a run of Inner Algorithm B with `β_t = β*_t`, then with probability at least
`1 - δ` the discrete-part regret satisfies
`R_{T₀,1} ≤ 2√(2dT₀β*_{T₀} log((dλ + T₀p²_max)/(dλ))) + 4p_max L‖θ̂ - θ₀‖₁T₀ + 2dp_max`. -/
theorem proposition_4 {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (θh : Fin d0 → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hgrid : M.pmax + 2 * l1 θh < d * M.pmax) (lam δ : ℝ) (hlam : 0 < lam)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (hEnv : IsPricingEnv M P 𝒢 x z p)
    (T0 : ℕ) (hT0 : 1 ≤ T0)
    (hrun : ∀ ω, ∃ j : ℕ → Fin d, IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
      (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
      ∀ ω ∈ E, discreteRegret M θh d x p T0 ω ≤
        2 * Real.sqrt (2 * d * T0 * betaStar M.pmax lam d δ T0 *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) +
        4 * M.pmax * L * l1 (θh - M.θ0) * T0 + 2 * d * M.pmax := by sorry

end LuoSunLiu.DIP
