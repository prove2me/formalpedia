-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_shadow_right_deriv
-- name    : LeviSampling.BaseStock.shadow_right_deriv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:18.90174+00:00
-- url     : https://prove2.me/theorems/13308760-5a8f-4906-b2b6-dad44d814d61
-- title:
--   Corollary 3.1 — the right derivative of the shadow cost is an expectation
-- statement:
--   Consider the multiperiod model with independent demands of finite mean and costs $h_i, b_i > 0$, periods $0$-based, $t < T$, and let $L_{t+1}, \dots, L_{T-1}$ be an upper base-stock policy. Then for every $y$, the right-hand derivative of $\tilde U_t$ at $y$ exists and equals
--   $$\tilde U^r_t(y) = \mathbb E\Big[-b_t + (h_t + b_t)\mathbb 1(D_t \le y) + \sum_{j=t+1}^{T-1} \tilde M^r_{tj}(y)\Big].$$
--   It is what makes the right derivative estimable by sampling paths.
--
--   **Formalization Note** "Right-hand derivative" is `HasDerivWithinAt` on $[y, \infty)$. The upper base-stock hypothesis is the setting in which the paper derives the formula (eq. (7) and p. 832).
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 834, Corollary 3.1 (with eq. (7))

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow
import Definitions.Def_LeviSampling_BaseStock_Estimator

open MeasureTheory

namespace LeviSampling.BaseStock

/-- **Corollary 3.1** (Levi, Roundy & Shmoys 2007, p. 834), 0-based periods. If
`L_{t+1}, …, L_{T-1}` is an upper base-stock policy, then for every `y` the right-hand derivative
of `Ũ_t` at `y` is `E[-b_t + (h_t + b_t) 𝟙(D_t ≤ y) + Σ_{j=t+1}^{T-1} M̃^r_{tj}(y)]`, the
expectation being over independent demands `D_0, …, D_{T-1}` with laws `μ 0, …, μ (T-1)`. -/
theorem shadow_right_deriv (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i)
    (L : ℕ → ℝ) (t : ℕ) (ht : t < T) (hL : IsUpperBaseStock T μ h b L (t + 1)) (y : ℝ) :
    HasDerivWithinAt (shadowU T μ h b L t)
      (∫ p, pathRightDeriv T h b L (extendPath p) t y ∂(pathLaw T μ)) (Set.Ici y) y := by sorry

end LeviSampling.BaseStock
