-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_pege_regret_bound
-- name    : LinParamBandits.PEGE.pege_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:29.441042+00:00
-- url     : https://prove2.me/theorems/aa4a6684-9e1c-4ca9-b03c-d95dae896402
-- title:
--   Theorem 3.1 — under SBAR(J), Regret(z,T,PEGE) ≤ a₁(‖z‖ + 1/‖z‖)r√T and Risk(T,PEGE) ≤ a₂ r√T
-- statement:
--   This is the main upper bound for the Phased Exploration and Greedy Exploitation policy.
--
--   1. Let $\sigma_0, \bar u, \lambda_0, J > 0$. There is a constant $a_1 > 0$, depending only on $\sigma_0, \bar u, \lambda_0, J$, such that for every dimension $r \ge 2$, every arm set $\mathcal U_r$, error laws and exploration arms satisfying Assumption 1 with these constants and the SBAR($J$) condition, every greedy rule, every $z \in \mathbb R^r \setminus \{0\}$ and every $T \ge r$,
--   $$\mathrm{Regret}(z, T, \mathrm{PEGE}) \le a_1 \Big(\|z\| + \frac{1}{\|z\|}\Big)\, r \sqrt T.$$
--   2. Let in addition $M > 0$. There is a constant $a_2 > 0$, depending only on $\sigma_0, \bar u, \lambda_0, J, M$, such that for every such $r$, instance and greedy rule, every prior $\mu$ on $\mathbb R^r$ with $\mathbb E[\|Z\|] \le M$ and $\mathbb E[1/\|Z\|] \le M$, and every $T \ge r$,
--   $$\mathrm{Risk}(T, \mathrm{PEGE}) \le a_2\, r \sqrt T.$$
--
--   Together with the lower bound of Theorem 2.1 this shows that PEGE attains the optimal order $r\sqrt T$ for arm sets with smooth best arm response, such as the unit sphere.
--
--   **Formalization Note** The constants are chosen before the dimension, the arm set, the error laws, the exploration arms, the greedy rule, the prior, $z$ and $T$; a constant allowed to depend on $r$ or on the instance would make the statement trivial, since the regret never exceeds $2\bar u\|z\|T$. The moments of $Z$ are lower Lebesgue integrals: $\mathbb E[1/\|Z\|]$ is $+\infty$ when $\mu$ charges the origin. Regret and risk take values in $[0, \infty]$, so the bounds also assert finiteness.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Theorem 3.1, p. 15

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Theorem 3.1 (Regret and Risk Under the Greedy Policy), Rusmevichientong, Tsitsiklis,
arXiv:0812.3465v2, p. 15. Under Assumption 1 and SBAR(`J`):

1. there is a positive constant `a₁`, depending only on `σ₀, ū, λ₀, J`, such that for any
   `z ∈ ℝ^r \ {0}` and `T ≥ r`, `Regret(z, T, PEGE) ≤ a₁ (‖z‖ + 1/‖z‖) r √T`;
2. if moreover `E[‖Z‖] ≤ M` and `E[1/‖Z‖] ≤ M` for every `r ≥ 2`, there is a positive constant `a₂`,
   depending only on `σ₀, ū, λ₀, J, M`, such that for any `T ≥ r`, `Risk(T, PEGE) ≤ a₂ r √T`.

The constants are chosen before the dimension `r`, the arm set, the error laws, the exploration
arms, the tie-breaking rule, the prior, `z` and `T`. -/
theorem pege_regret_bound :
    (∀ σ₀ ū lam₀ J : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ → 0 < J →
      ∃ a₁ : ℝ, 0 < a₁ ∧
        ∀ (r : ℕ), 2 ≤ r →
        ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
          (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
        Assumption1 𝒰 ν b σ₀ ū lam₀ → SBAR 𝒰 J → GreedySelector 𝒰 g →
        ∀ (z : LinParamBandits.LowerBound.Vec r), z ≠ 0 → ∀ (T : ℕ), r ≤ T →
          regret 𝒰 ν b g z T ≤ ENNReal.ofReal (a₁ * (‖z‖ + 1 / ‖z‖) * r * Real.sqrt T)) ∧
    (∀ σ₀ ū lam₀ J M : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ → 0 < J → 0 < M →
      ∃ a₂ : ℝ, 0 < a₂ ∧
        ∀ (r : ℕ), 2 ≤ r →
        ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
          (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
        Assumption1 𝒰 ν b σ₀ ū lam₀ → SBAR 𝒰 J → GreedySelector 𝒰 g →
        ∀ (μ : Measure (LinParamBandits.LowerBound.Vec r)), IsProbabilityMeasure μ →
          ∫⁻ z, ‖z‖ₑ ∂μ ≤ ENNReal.ofReal M → ∫⁻ z, ‖z‖ₑ⁻¹ ∂μ ≤ ENNReal.ofReal M →
        ∀ (T : ℕ), r ≤ T →
          risk μ 𝒰 ν b g T ≤ ENNReal.ofReal (a₂ * r * Real.sqrt T)) := by sorry
end LinParamBandits.PEGE
