-- Prove2me | Theorems.Thm_LinParamBandits_UEFinite_gap_min_expectation_bound
-- name    : LinParamBandits.UEFinite.gap_min_expectation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:44.43498+00:00
-- url     : https://prove2.me/theorems/49b453eb-eb6f-4d2e-8b06-ce0b68bf063b
-- title:
--   Proof of Theorem 4.2 — E[min{log T/Δ^u(Z), TΔ^u(Z)}] ≤ (M₀+1) log T + M₀ log² T
-- statement:
--   Let $r \ge 2$, let $\mathcal U_r \subset \mathbb R^r$ be a finite nonempty set of arms, $u \in \mathcal U_r$, and $\Delta^u(z) = \max_{v \in \mathcal U_r} v'z - u'z$. Let $Z$ have a probability law $\mu$ on $\mathbb R^r$ such that the law of $\Delta^u(Z)$ consists of a point mass at $0$ and a density bounded above by $M_0 > 0$ on $\mathbb R_+$. Then for every $T \ge r + 1$ the random variable $\min\{\log T/\Delta^u(Z), T\Delta^u(Z)\}$ is integrable and
--   $$\mathbb E\Big[\min\Big\{\frac{\log T}{\Delta^u(Z)}, T\Delta^u(Z)\Big\}\Big] \le (M_0 + 1)\log T + M_0\log^2 T.$$
--
--   Integrated against the prior, the per-arm term of the regret bound of Theorem 4.2 grows like $\log^2 T$; this is what turns the $\log T$ regret bound into the $|\mathcal U_r|^2\log^2 T$ Bayes risk bound.
--
--   **Formalization Note** On the event $\Delta^u(Z) = 0$ the minimum is read as $0$ (the paper's $\min\{\log T/0, 0\}$); Lean's convention $x/0 = 0$ gives the same value. The density condition is written as: the law of $\Delta^u(Z)$ restricted to $(0, \infty)$ is at most $M_0$ times Lebesgue measure. Assumption 1 and the policy play no role in this statement and are not assumed.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, proof of Theorem 4.2, pp. 22–23, display after 'From the regret bound, it suffices to show that for any u ∈ U_r'

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

theorem gap_min_expectation_bound
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite) (h𝒰ne : 𝒰.Nonempty)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (μ : Measure (LinParamBandits.LowerBound.Vec r)) (hμ : IsProbabilityMeasure μ)
    (M₀ : ℝ) (hM₀ : 0 < M₀) (hdens : GapDensityLe 𝒰 μ M₀ u) (T : ℕ) (hT : r + 1 ≤ T) :
    Integrable (fun z => min (Real.log T / gap 𝒰 u z) (T * gap 𝒰 u z)) μ ∧
    ∫ z, min (Real.log T / gap 𝒰 u z) (T * gap 𝒰 u z) ∂μ ≤
      (M₀ + 1) * Real.log T + M₀ * Real.log T ^ 2 := by sorry

end LinParamBandits.UEFinite
