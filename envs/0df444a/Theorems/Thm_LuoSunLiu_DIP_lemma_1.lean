-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_lemma_1
-- name    : LuoSunLiu.DIP.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:03.401819+00:00
-- url     : https://prove2.me/theorems/efe70a24-b51b-46ae-bfae-861e0584073e
-- title:
--   Lemma 1, p. 14 — ‖ξ_t − ξ*‖_∞ ≤ L‖θ̂ − θ₀‖₁, and the single-episode pricing problem is a PLB with perturbation 2L‖θ̂ − θ₀‖₁
-- statement:
--   Let $F$ be $L$-Lipschitz (Assumption 1). Fix an estimate $\hat\theta \in \mathbb R^{d_0}$ and a discretization number $d \ge 1$, and let the prices be predictable and lie in the candidate sets: $p_t = m_{j_t} + x_t^\top\hat\theta$ with $j_t \in \mathcal B_t$ for every $t \ge 1$. Write $\xi_t = (1 - F(m_j + x_t^\top\hat\theta - x_t^\top\theta_0))_j$ and $\xi^* = (1 - F(m_j))_j$.
--
--   1. For every $t \ge 1$,
--   $$\|\xi_t - \xi^*\|_\infty \le L\,\|\hat\theta - \theta_0\|_1 .$$
--   2. Under the price-action coupling $A_t = p_t e_{j_t}$, with action sets $\mathcal A_t = \{p\,e_j : j \in \mathcal B_t,\ p = m_j + x_t^\top\hat\theta\}$, reward $Z_t = p_t y_t$ and noise $\eta_t = Z_t - \langle\xi_t, A_t\rangle$, the processes form a perturbed linear bandit with respect to the filtration $\mathcal G$: $A_t \in \mathcal A_t$ is $\mathcal G_{t-1}$-measurable, $\eta_t$ is $\mathcal G_t$-measurable and $p_{\max}$-sub-Gaussian conditionally on $\mathcal G_{t-1}$ ($\mathbb E[e^{u\eta_t}\mid\mathcal G_{t-1}] \le e^{p_{\max}^2u^2/2}$), and the perturbation constant is
--   $$\|\xi_s - \xi_t\|_\infty \le 2L\,\|\hat\theta - \theta_0\|_1 \quad (s, t \ge 1).$$
--
--   The lemma turns the pricing problem of one episode into a perturbed linear bandit whose perturbation is proportional to the estimation error, which is what Lemma 3 analyses.
--
--   **Formalization Note** The statement holds for any predictable prices in the candidate sets, not only for Algorithm 3. Conditional sub-Gaussianity is stated for the filtration $\mathcal G$, which contains the paper's $\mathcal F_{t-1} = \sigma(\xi_1, A_1, Z_1, \dots, \xi_t, A_t)$; the paper proves it for $\sigma(x_1, p_1, Z_1, \dots, x_t, p_t)$ and passes to $\mathcal F_{t-1}$ by the tower property (pp. 35–36), so the $\mathcal G$ version is at least as strong. The variance proxy is $p_{\max}^2$ (the conditional Hoeffding lemma, platform theorem `hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero`, is the related tool). The standing assumptions of the model, a standard Borel sample space and a probability measure are assumed. Arms are 0-based (`Fin d`).
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 14, Lemma 1; proof pp. 34–36

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Definitions.Def_LuoSunLiu_DIP_PLB

open MeasureTheory ProbabilityTheory NNReal

namespace LuoSunLiu.DIP

/-- Lemma 1 (Luo, Sun and Liu, arXiv:2109.07340v2, p. 14; proof pp. 34–36). For a single
episode with a fixed estimate `θ̂` and `d` grid points, and any predictable prices
`p_t = m_{j_t} + x_tᵀθ̂ ∈ 𝒮_t`: (i) `‖ξ_t - ξ*‖_∞ ≤ L‖θ̂ - θ₀‖₁`; (ii) with the price-action
coupling `A_t = Q_t(p_t) = p_t e_{j_t}` and reward `Z_t = p_t y_t`, the processes form a
perturbed linear bandit whose noise `η_t = Z_t - ⟨ξ_t, A_t⟩` is `p_max`-sub-Gaussian
conditionally on `𝒢_{t-1}`, with perturbation constant `2L‖θ̂ - θ₀‖₁`. -/
theorem lemma_1 {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (θh : Fin d0 → ℝ) (d : ℕ) (hd : 1 ≤ d)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (hEnv : IsPricingEnv M P 𝒢 x z p)
    (j : ℕ → Ω → Fin d)
    (hj : ∀ t : ℕ, 1 ≤ t → ∀ ω, j t ω ∈ avail M.pmax θh d (x t ω) ∧
      p t ω = gridPrice M.pmax θh d (j t ω) (x t ω)) :
    (∀ t : ℕ, 1 ≤ t → ∀ ω i,
      |xiPricing M θh d (x t ω) i - xiStar M θh d i| ≤ L * l1 (θh - M.θ0)) ∧
    IsPLBModel P 𝒢 (fun t ω => xiPricing M θh d (x t ω))
      (fun t ω => pricingActions M θh d (x t ω))
      (fun t ω => Pi.single (j t ω) (p t ω))
      (fun t ω => p t ω * response M x z p t ω)
      (fun t ω => p t ω * response M x z p t ω -
        xiPricing M θh d (x t ω) ⬝ᵥ Pi.single (j t ω) (p t ω))
      (Real.toNNReal M.pmax ^ 2) ∧
    HasPerturbation (fun t ω => xiPricing M θh d (x t ω)) (2 * L * l1 (θh - M.θ0)) := by sorry

end LuoSunLiu.DIP
