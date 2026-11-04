-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_proposition_3_conditional
-- name    : LuoSunLiu.DIP.proposition_3_conditional
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T04:37:25.008201+00:00
-- url     : https://prove2.me/theorems/025b4ef5-a691-4714-8ad2-1178ff9104a8
-- title:
--   Proof of Theorem 1, p. 55 — Proposition 3(b) for an episode with a random 𝒢_{s₀}-measurable estimate: E(R'_k) ≤ C′₃ log(C′₂T₀)T₀^{2/3} + 4p_max L T₀ E‖θ̂ − θ₀‖₁
-- statement:
--   This is Proposition 3(b) applied to one episode of the DIP policy whose input estimate is random, as used in the proof of Theorem 1.
--
--   Let the standing assumptions of the contextual pricing model hold ($\|\theta_0\|_1 \le W$, $p_{\max} > 0$, $\|x\|_\infty \le 1$ on $\mathcal X$, and $p^*(x) \in (0, p_{\max})$ maximizes $p \mapsto p(1 - F(p - x^\top\theta_0))$ over $p > 0$), let $F$ be $L$-Lipschitz (Assumption 1), and let Assumption 2 hold with constant $C_A$. Fix a discretization constant $C_d \in \mathbb N$ with $p_{\max} + 2W < C_d\,p_{\max}$ and a regularization parameter $\lambda > 0$.
--
--   Then there are constants $C'_2, C'_3 > 0$ with the following property. Let $(\Omega, \mathcal F, \mathbb P)$ be a probability space on a standard Borel space with a filtration $(\mathcal G_t)$, and let covariates $x_t$, prices $p_t$ and noise $z_t$ form a pricing environment (covariates and prices $\mathcal G_{t-1}$-measurable, $z_t$ $\mathcal G_t$-measurable with CDF $F$ and independent of $\mathcal G_{t-1}$). Consider an episode of $T_0 \ge 1$ periods $s_0 + 1, \dots, s_0 + T_0$ and a random estimate $\hat\theta$ that is $\mathcal G_{s_0}$-measurable with $\|\hat\theta\|_1 \le W$. Suppose that on every sample path the prices of the episode are a run of Inner Algorithm B with input $\hat\theta$, $d = C_d\lceil T_0^{1/6}\rceil$ grid points, confidence level $\delta = 1/T_0$, confidence parameters $\beta_\tau = \beta^*_\tau$ and regularization $\lambda$. Then
--
--   $$\mathbb E\Big[\sum_{t = s_0 + 1}^{s_0 + T_0} r_t\Big] \le C'_3\log(C'_2T_0)\,T_0^{2/3} + 4p_{\max}L\,T_0\,\mathbb E\|\hat\theta - \theta_0\|_1,$$
--
--   where $r_t$ is the per-period regret (1).
--
--   In the proof of Theorem 1 this is the step $\mathbb E(R'_k \mid \hat\theta_{k-1}) \le C'_3\log(C'_2\ell_k)\ell_k^{2/3} + 4L\|\theta_0 - \hat\theta_{k-1}\|_1p_{\max}\ell_k$ followed by taking expectations: it is Proposition 3 (whose estimate is deterministic and whose episode starts at period 1) applied conditionally on the history up to the start of the episode. It is the only probabilistic input needed to sum the episode regrets of DIP into Theorem 1.
--
--   **Formalization Note** The constants are chosen exactly as in Proposition 3(b): after $C_d$ and $\lambda$ and before the probability space, the episode start $s_0$, the length $T_0$ and the estimate. Expectations are lower Lebesgue integrals of nonnegative quantities, written with `ENNReal.ofReal`.
-- source:
--   Luo, Sun and Liu, Distribution-free contextual dynamic pricing, arXiv:2109.07340v2, proof of Theorem 1, p. 55 (the step 'For the regret R'_k in episode 2 ≤ k ≤ n, we have by Proposition 3, E(R'_k | θ̂_{k−1}) ≤ ... Therefore, we obtain E(R'_k) ≤ ...'), applying Proposition 3 (pp. 22–23, proof pp. 52–54)

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace LuoSunLiu.DIP

/-- Proposition 3(b) applied to an episode with a random, previously computed estimate (Luo, Sun
and Liu, arXiv:2109.07340v2, proof of Theorem 1, p. 55: "for the regret `R'_k` in episode
`2 ≤ k ≤ n`, we have by Proposition 3, `E(R'_k | θ̂_{k-1}) ≤ C′₃ log(C′₂ℓ_k)ℓ_k^{2/3} +
4L‖θ₀ - θ̂_{k-1}‖₁p_max ℓ_k`; therefore `E(R'_k) ≤ C′₃ log(C′₂ℓ_k)ℓ_k^{2/3} +
4p_max L E‖θ̂_{k-1} - θ₀‖₁ ℓ_k`"). For every discretization constant `C_d` with
`p_max + 2W < C_d p_max` and every `λ > 0` there are constants `C′₂, C′₃ > 0` such that: for every
pricing environment, every episode of `T₀ ≥ 1` periods `s₀ + 1, …, s₀ + T₀`, and every estimate
`θ̂` that is `𝒢_{s₀}`-measurable with `‖θ̂‖₁ ≤ W`, if on every sample path the prices of the
episode are a run of Inner Algorithm B with input `θ̂`, `d = C_d⌈T₀^{1/6}⌉`, `δ = 1/T₀` and
`β = β*`, then the expected regret of the episode is at most
`C′₃ log(C′₂T₀) T₀^{2/3} + 4p_max L T₀ E‖θ̂ - θ₀‖₁`. -/
theorem proposition_3_conditional {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (CA : ℝ) (hA2 : Assumption2 M CA)
    (Cdisc : ℕ) (hCdisc : M.pmax + 2 * M.W < Cdisc * M.pmax) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C2' C3' : ℝ, 0 < C2' ∧ 0 < C3' ∧
      ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
        (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ), IsPricingEnv M P 𝒢 x z p →
      ∀ (s0 T0 : ℕ), 1 ≤ T0 →
      ∀ (θh : Ω → Fin d0 → ℝ), Measurable[𝒢 s0] θh → (∀ ω, l1 (θh ω) ≤ M.W) →
      (∀ ω, ∃ j : ℕ → Fin (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊),
        IsInnerBRun M.pmax (θh ω) lam
          (betaStar M.pmax lam (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊) (1 / (T0 : ℝ))) s0 T0
          (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) →
      ∫⁻ ω, ENNReal.ofReal (∑ t ∈ Finset.Icc (s0 + 1) (s0 + T0), perRegret M (x t ω) (p t ω)) ∂P ≤
        ENNReal.ofReal (C3' * Real.log (C2' * T0) * (T0 : ℝ) ^ ((2 : ℝ) / 3)) +
          ENNReal.ofReal (4 * M.pmax * L * T0) *
            ∫⁻ ω, ENNReal.ofReal (l1 (θh ω - M.θ0)) ∂P := by sorry

end LuoSunLiu.DIP
