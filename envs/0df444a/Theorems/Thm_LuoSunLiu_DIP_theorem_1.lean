-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_theorem_1
-- name    : LuoSunLiu.DIP.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:52.454438+00:00
-- url     : https://prove2.me/theorems/b1559e7b-6801-4cc7-b419-b3fe537e197f
-- title:
--   Theorem 1, p. 18 — DIP has E(R_T) ≤ C T^{2/3} log T + 4p_max L Σ_k 2^{k−2}ℓ₂ E‖θ̂_{k−1} − θ₀‖₁ (Õ pinned from the proof, pp. 54–55)
-- statement:
--   This is the main regret bound of the DIP policy.
--
--   Let the standing assumptions of the contextual pricing model hold ($\|\theta_0\|_1 \le W$, $p_{\max} > 0$, $\|x\|_\infty \le 1$ on $\mathcal X$, and $p^*(x) \in (0, p_{\max})$ maximizes the expected revenue $p(1 - F(p - x^\top\theta_0))$ over $p > 0$), let $F$ be $L$-Lipschitz (Assumption 1), and let Assumption 2 hold. Fix DIP inputs $\alpha_1, \alpha_2 \ge 1$ (so $\ell_1 = \alpha_1$, $\ell_2 = \alpha_2$), a discretization constant $C_d$ with $p_{\max} + 2W < C_d\,p_{\max}$, and $\lambda > 0$.
--
--   Then there is a constant $C > 0$ with the following property. On any probability space with a filtration, for any adapted covariates, i.i.d. noise with CDF $F$, any admissible Inner Algorithm A (a measurable estimator of the previous episode's data with values in $\{\|\theta\|_1 \le W\}$) and any run of the DIP policy, for every horizon $T \ge 2$,
--   $$\mathbb E(R_T) \le C\,T^{2/3}\log T + 4p_{\max}L\sum_{k=2}^{n}2^{k-2}\ell_2\,\mathbb E\|\hat\theta_{k-1} - \theta_0\|_1,$$
--   where $R_T = \sum_{t=1}^T r_t$ is the cumulative regret (1) and $n = n(T, \alpha_1, \alpha_2)$ is the number of episodes up to $T$.
--
--   The first term is the price of learning the unknown noise distribution by discretized UCB pricing; the second isolates the contribution of the estimation errors of $\theta_0$, so that any estimator with a known $\ell_1$ error rate yields an explicit regret rate for DIP.
--
--   **Formalization Note** The printed $\tilde O(T^{2/3})$ is pinned to $C\,T^{2/3}\log T$ for $T \ge 2$: the proof (p. 55) gives $\ell_1p_{\max} + C'_3C_4\log(2C'_2T)T^{2/3}$, which this absorbs. The constant $C$ depends only on the model, $L$, the Assumption 2 constant, $\alpha_1, \alpha_2, C_d$ and $\lambda$, and is chosen before the probability space, the processes, the estimator and $T$; this is what the proof supports and is stronger than a constant chosen per run. Inner Algorithm A is any admissible estimator, with the paper's Algorithm 2 (logistic regression, then projection onto $\{\|\theta\|_1 \le W\}$) as one instance. Algorithm 3 is read with forced exploration of unpulled arms (Lemma 2's convention). The grid hypothesis $p_{\max} + 2W < C_d\,p_{\max}$ makes every candidate price set nonempty, without which the policy is undefined. The noise is independent of the past and the covariates are predictable for a general filtration, which needs a standard Borel sample space. For the last, truncated episode the weight is $2^{n-2}\ell_2$, as printed. Expectations are lower Lebesgue integrals of nonnegative quantities.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 18, Theorem 1; proof pp. 54–55

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Definitions.Def_LuoSunLiu_DIP_Policy

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace LuoSunLiu.DIP

/-- Theorem 1 (Luo, Sun and Liu, arXiv:2109.07340v2, p. 18; proof pp. 54–55), with the `Õ(T^{2/3})`
pinned to `C T^{2/3} log T`. Under the standing assumptions of §2.1 and Assumptions 1–2, for DIP
inputs `α₁, α₂ ≥ 1`, `C` (here `Cdisc`) with `p_max + 2W < C p_max`, and `λ > 0`, there is a
constant `C₀ > 0` such that for every probability space, filtration, adapted covariates, i.i.d.
noise, admissible estimator (Inner Algorithm A) and every run of the DIP policy, and every
`T ≥ 2`,
`E(R_T) ≤ C₀ T^{2/3} log T + 4p_max L ∑_{k=2}^{n} 2^{k-2}ℓ₂ E‖θ̂_{k-1} - θ₀‖₁`,
where `n = n(T, α₁, α₂)` is the number of episodes up to `T` and `ℓ₂ = α₂`. -/
theorem theorem_1 {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (CA : ℝ) (hA2 : Assumption2 M CA)
    (α1 α2 Cdisc : ℕ) (hα1 : 1 ≤ α1) (hα2 : 1 ≤ α2)
    (hCdisc : M.pmax + 2 * M.W < Cdisc * M.pmax) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
        (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ)
        (est : (k : ℕ) → (Fin (epLen α1 α2 k) → (Fin d0 → ℝ) × ℝ × ℝ) → (Fin d0 → ℝ)),
        IsPricingEnv M P 𝒢 x z p → IsAdmissibleEstimator M α1 α2 est →
        (∀ ω, IsDIPRun M α1 α2 Cdisc lam est x z p ω) →
        ∀ T : ℕ, 2 ≤ T →
          ∫⁻ ω, ENNReal.ofReal (cumRegret M x p T ω) ∂P ≤
            ENNReal.ofReal (C * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.log T) +
              ENNReal.ofReal (4 * M.pmax * L) *
                ∑ k ∈ Finset.Icc 2 (nEp α1 α2 T),
                  ((2 ^ (k - 2) * α2 : ℕ) : ℝ≥0∞) *
                    ∫⁻ ω, ENNReal.ofReal
                      (l1 (thetaHat M α1 α2 est x z p (k - 1) ω - M.θ0)) ∂P := by sorry

end LuoSunLiu.DIP
