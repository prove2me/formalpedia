-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_mean_value_inequality
-- name    : HunterPDE.Harmonic.mean_value_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:04:04.869989+00:00
-- url     : https://prove2.me/theorems/fcdf3f31-9180-4402-88d6-f73dcbb6a833
-- title:
--   Theorem 2.5 — mean value inequalities for sub- and superharmonic functions
-- statement:
--   Let $n \ge 1$, let $\Omega \subseteq \mathbb{R}^n$ be open, $B_r(x) \Subset \Omega$ and $u \in C^2(\Omega)$. If $u$ is subharmonic in $\Omega$ ($\Delta u \ge 0$), then
--   $$u(x) \le ⨍_{B_r(x)} u \, dx, \qquad u(x) \le ⨍_{\partial B_r(x)} u \, dS. \qquad (2.5)$$
--   If $u$ is superharmonic in $\Omega$ ($\Delta u \le 0$), then
--   $$u(x) \ge ⨍_{B_r(x)} u \, dx, \qquad u(x) \ge ⨍_{\partial B_r(x)} u \, dS. \qquad (2.6)$$
--
--   The inequality (2.5) is what the proof of the strong maximum principle (Theorem 2.13) uses.
--
--   **Formalization Note.** Sub- and superharmonicity (Definition 2.4, including $u \in C^2(\Omega)$) are the definition item `Subharmonic`; the averages are those of `MeanValue`. $B_r(x) \Subset \Omega$ is `0 < r` and `Metric.closedBall x r ⊆ Ω`. The two cases are stated as a conjunction of two implications. $n \ge 1$ keeps the sphere nonempty.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 22, Theorem 2.5

import Mathlib
import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Definitions.Def_HunterPDE_Harmonic_Subharmonic

open MeasureTheory

namespace HunterPDE.Harmonic

/-- Theorem 2.5 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 22: let `Ω ⊆ ℝⁿ` be open,
`B_r(x) ⋐ Ω` (the closed ball lies in `Ω`, `r > 0`) and `u ∈ C²(Ω)`. If `u` is subharmonic in `Ω`
(`Δu ≥ 0`), then `u(x)` is at most its average over the ball `B_r(x)` and at most its average over
the sphere `∂B_r(x)` (2.5); if `u` is superharmonic in `Ω` (`Δu ≤ 0`), both inequalities are
reversed (2.6). The `C²` hypothesis is part of `IsSubharmonicOn` / `IsSuperharmonicOn`
(Definition 2.4). `n ≥ 1`, so that the sphere is nonempty. -/
theorem mean_value_inequality {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Ω) :
    (IsSubharmonicOn Ω u →
        u x ≤ (⨍ y in Metric.ball x r, u y) ∧ u x ≤ sphereAverage u x r) ∧
      (IsSuperharmonicOn Ω u →
        (⨍ y in Metric.ball x r, u y) ≤ u x ∧ sphereAverage u x r ≤ u x) := by sorry

end HunterPDE.Harmonic
