-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_cycle_sum_regret
-- name    : LinParamBandits.PEGE.cycle_sum_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:32.66107+00:00
-- url     : https://prove2.me/theorems/daf80908-49db-4213-8e3b-a2b404ea3266
-- title:
--   Sec. 3.1, p. 18 — regret after K cycles ≤ h₃ r‖z‖K + h₄ Σ_{c≤K} r/‖z‖
-- statement:
--   Under Assumption 1 with constants $\sigma_0, \bar u, \lambda_0 > 0$ and the SBAR($J$) condition with $J > 0$, there are constants $h_3, h_4 > 0$, depending only on $\sigma_0, \bar u, \lambda_0, J$, such that for every dimension $r \ge 2$, every instance satisfying these conditions, every greedy rule, every $z \in \mathbb R^r \setminus \{0\}$ and every number of cycles $K \ge 1$,
--   $$\mathrm{Regret}\Big(z,\ rK + \sum_{c=1}^K c,\ \mathrm{PEGE}\Big) \le h_3\, r\, \|z\|\, K + h_4 \sum_{c=1}^K \frac{r}{\|z\|}.$$
--
--   The horizon $rK + \sum_{c=1}^K c$ is the end of cycle $K$. The first term collects the exploration periods, the second the exploitation periods; Theorem 3.1 follows by choosing $K$ of order $\sqrt T$.
--
--   **Formalization Note** The display on p. 18 carries no explicit hypothesis on $z$; it is derived from Lemma 3.6, which needs $z \ne 0$, and its right side is undefined at $z = 0$, so $z \ne 0$ is assumed.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Sec. 3.1, p. 18, display after 'Summing over K cycles, we obtain'

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Sec. 3.1, p. 18, display after "Summing over K cycles, we obtain" (Rusmevichientong,
Tsitsiklis, arXiv:0812.3465v2): under Assumption 1 and SBAR(`J`) there are positive constants
`h₃, h₄`, depending only on `σ₀, ū, λ₀, J`, such that for `z ≠ 0` and `K ≥ 1`,
`Regret(z, rK + ∑_{c=1}^K c, PEGE) ≤ h₃ r ‖z‖ K + h₄ ∑_{c=1}^K r / ‖z‖`. -/
theorem cycle_sum_regret (σ₀ ū lam₀ J : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (hJ : 0 < J) :
    ∃ h₃ h₄ : ℝ, 0 < h₃ ∧ 0 < h₄ ∧
      ∀ (r : ℕ), 2 ≤ r →
      ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
        (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
      Assumption1 𝒰 ν b σ₀ ū lam₀ → SBAR 𝒰 J → GreedySelector 𝒰 g →
      ∀ (z : LinParamBandits.LowerBound.Vec r), z ≠ 0 → ∀ (K : ℕ), 1 ≤ K →
        regret 𝒰 ν b g z (r * K + ∑ c ∈ Finset.Icc 1 K, c)
          ≤ ENNReal.ofReal (h₃ * r * ‖z‖ * K + h₄ * ∑ c ∈ Finset.Icc 1 K, (r / ‖z‖)) := by sorry
end LinParamBandits.PEGE
