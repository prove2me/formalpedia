-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_lemma_S5
-- name    : LuoSunLiu.DIP.lemma_S5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:29.23543+00:00
-- url     : https://prove2.me/theorems/ba830187-b324-4a0c-99aa-cac09fb969f9
-- title:
--   Lemma S5, pp. 40–41 — w.p. ≥ 1 − δ, ‖ξ̇_t − ξ̂_{t−1}‖_{V_{t−1}(λ)} ≤ C₁√(λd) + √(2 log(1/δ) + d log((dλ + (t−1)a²_max)/(dλ))) for all t ≥ 2
-- statement:
--   Consider a perturbed linear bandit in dimension $d \ge 1$ with conditionally $1$-sub-Gaussian noise (Condition 4) that satisfies Condition 2 ($\|\xi_t\|_\infty \le C_1$, $C_1 \ge 0$) and Condition 3 (one nonzero entry and $\|a\|_2 \le a_{\max}$, $a_{\max} > 0$). Let $\lambda > 0$ and $\delta \in (0, 1)$. Then with probability at least $1 - \delta$, simultaneously for all $t \ge 2$,
--   $$\|\dot\xi_t - \hat\xi_{t-1}\|_{V_{t-1}(\lambda)} \le C_1\sqrt{\lambda d} + \sqrt{2\log(1/\delta) + d\log\frac{d\lambda + (t-1)a_{\max}^2}{d\lambda}},$$
--   where $\hat\xi_{t-1} = V_{t-1}(\lambda)^{-1}\sum_{s=1}^{t-1}A_sZ_s$ is the ridge estimate and $\dot\xi_t$ the shadow parameter of Lemma S3.
--
--   This is the confidence ellipsoid that drives the optimism argument of Lemma 3.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: there is a measurable event of probability at least $1 - \delta$ on which the bound holds for every $t \ge 2$. This is the inner-measure reading and does not depend on the measurability of the bound's event. The actions need not follow M-LinUCB: any predictable actions in the action sets are allowed, as in the paper's proof.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, pp. 40–41, Lemma S5

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_LuoSunLiu_DIP_PLB

open MeasureTheory ProbabilityTheory Matrix

namespace LuoSunLiu.DIP

/-- Lemma S5 (Luo, Sun and Liu, arXiv:2109.07340v2, pp. 40–41). In a perturbed linear bandit
whose noise is conditionally 1-sub-Gaussian (Condition 4) and which satisfies Conditions 2–3, for
any `λ > 0` and `δ ∈ (0, 1)`, with probability at least `1 - δ` it holds simultaneously for all
`t ≥ 2` that
`‖ξ̇_t - ξ̂_{t-1}‖_{V_{t-1}(λ)} ≤ C₁√(λd) + √(2 log(1/δ) + d log((dλ + (t-1)a²_max)/(dλ)))`.
"With probability at least `1 - δ`" is stated as: some measurable event of probability at least
`1 - δ` is contained in the event. -/
theorem lemma_S5 {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (ξ : ℕ → Ω → Fin d → ℝ) (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) (A : ℕ → Ω → Fin d → ℝ)
    (Z η : ℕ → Ω → ℝ) (C1 amax lam δ : ℝ)
    (hPLB : IsPLBModel P ℱ ξ 𝒜 A Z η 1) (hCond2 : Condition2 ξ C1)
    (hCond3 : Condition3 𝒜 amax) (hC1 : 0 ≤ C1) (hamax : 0 < amax) (hlam : 0 < lam)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
      ∀ ω ∈ E, ∀ t : ℕ, 2 ≤ t →
        mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)
            (shadowParam A ξ t ω - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ≤
          C1 * Real.sqrt (lam * d) +
            Real.sqrt (2 * Real.log (1 / δ) +
              d * Real.log ((d * lam + ((t : ℝ) - 1) * amax ^ 2) / (d * lam))) := by sorry

end LuoSunLiu.DIP
