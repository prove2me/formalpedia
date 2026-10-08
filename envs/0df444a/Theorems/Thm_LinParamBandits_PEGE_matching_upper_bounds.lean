-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_matching_upper_bounds
-- name    : LinParamBandits.PEGE.matching_upper_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:38.908748+00:00
-- url     : https://prove2.me/theorems/5e0fd74b-de61-493e-825c-65fd9ef7cc8d
-- title:
--   Corollary 3.3 — on the unit sphere with N(0,1) errors, PEGE has Regret ≤ a₃(‖z‖ + 1/‖z‖)r√T and Risk ≤ a₃ r√T
-- statement:
--   Consider the bandit problem whose set of arms is the unit sphere of $\mathbb R^r$ and whose errors $W^u_t$ are standard normal for all $t$ and $u$. There is an absolute constant $a_3 > 0$ such that for every $r \ge 2$, every choice of the exploration arms and every greedy rule:
--   1. for every $z \in \mathbb R^r \setminus \{0\}$ and every $T \ge r$,
--   $$\mathrm{Regret}(z, T, \mathrm{PEGE}) \le a_3\Big(\|z\| + \frac{1}{\|z\|}\Big) r\sqrt T;$$
--   2. if $Z$ has the multivariate normal distribution with mean $0$ and covariance matrix $I_r/r$, then for every $T \ge r$,
--   $$\mathrm{Risk}(T, \mathrm{PEGE}) \le a_3\, r \sqrt T.$$
--
--   Together with Theorem 2.1, this shows that the $r\sqrt T$ lower bound is attained on the unit sphere.
--
--   **Formalization Note** PEGE explores the arms $b_1, \dots, b_r$ of Assumption 1(b); the proof of the corollary uses Assumption 1 with $\sigma_0 = \bar u = \lambda_0 = 1$, so the exploration arms are taken on the sphere with $\lambda_{\min}(\sum_k b_kb_k') \ge 1$ (which forces them to be orthonormal).
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Corollary 3.3, p. 16

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Corollary 3.3 (Matching Upper Bounds), Rusmevichientong, Tsitsiklis,
arXiv:0812.3465v2, p. 16: arms on the unit sphere of `ℝ^r`, every error standard normal. There is
an absolute constant `a₃` such that for any `z ∈ ℝ^r \ {0}` and `T ≥ r`,
`Regret(z, T, PEGE) ≤ a₃ (‖z‖ + 1/‖z‖) r √T`, and, if `Z ~ N(0, I_r/r)`, `Risk(T, PEGE) ≤ a₃ r √T`
for all `T ≥ r`. PEGE explores the arms `b_k` of Assumption 1(b) with `ū = λ₀ = 1`, the values the
proof of the corollary uses. -/
theorem matching_upper_bounds :
    ∃ a₃ : ℝ, 0 < a₃ ∧
      ∀ (r : ℕ), 2 ≤ r →
      ∀ (b : Fin r → LinParamBandits.LowerBound.Vec r) (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
      ArmAssumption (Metric.sphere (0 : LinParamBandits.LowerBound.Vec r) 1) b 1 1 →
      GreedySelector (Metric.sphere (0 : LinParamBandits.LowerBound.Vec r) 1) g →
        (∀ (z : LinParamBandits.LowerBound.Vec r), z ≠ 0 → ∀ (T : ℕ), r ≤ T →
          regret (Metric.sphere (0 : LinParamBandits.LowerBound.Vec r) 1) stdNormalNoise b g z T
            ≤ ENNReal.ofReal (a₃ * (‖z‖ + 1 / ‖z‖) * r * Real.sqrt T)) ∧
        (∀ (T : ℕ), r ≤ T →
          risk (gaussPrior r) (Metric.sphere (0 : LinParamBandits.LowerBound.Vec r) 1) stdNormalNoise b g T
            ≤ ENNReal.ofReal (a₃ * r * Real.sqrt T)) := by sorry
end LinParamBandits.PEGE
