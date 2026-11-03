-- Prove2me | Theorems.Thm_HryniewiczCriterion_czIndexOfPath_eq_of_polarAngleLift
-- name    : HryniewiczCriterion.czIndexOfPath_eq_of_polarAngleLift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:02:02.985795+00:00
-- url     : https://prove2.me/theorems/fd2a8f2e-9aca-4904-8dc8-914a30c4fedd
-- title:
--   Hryniewicz's index of a path in SL(2,R) from its polar rotation angle
-- statement:
--   Let $\varphi:\mathbb{R}\to M_2(\mathbb{R})$ be continuous on $[0,1]$ with $\varphi(0)=\mathrm{Id}$ and $\det\varphi(1)=1$, and let $\alpha$ be a continuous polar angle of $\varphi$ on $[0,1]$: $\alpha(0)=0$ and $\varphi(t)=R(\alpha(t))P(t)$ with $P(t)$ symmetric positive definite, where $R(a)$ is the rotation by $a$. Let $\mu(\varphi)$ be Hryniewicz's index of $\varphi$, defined from its winding interval, and let $k\in\mathbb{Z}$.
--
--   1. If $\operatorname{tr}\varphi(1)>2$ and $|\alpha(1)-2\pi k|<\pi/2$, then $\mu(\varphi)=2k$.
--   2. If $\operatorname{tr}\varphi(1)<2$ and $2\pi k<\alpha(1)<2\pi k+2\pi$, then $\mu(\varphi)=2k+1$.
--
--   This computes Hryniewicz's index of a path in $\mathrm{SL}(2,\mathbb{R})$ from its polar rotation angle and the trace of its end point. The path need only be continuous.
--
--   **Formalization Note** $\mu$ is `HryniewiczCriterion.czIndexOfPath`, and the polar angle is `HryniewiczCriterion.IsPolarAngleLift`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1.1

import Definitions.Def_HryniewiczCriterion_GraphAngle

namespace HryniewiczCriterion

/-- For a continuous path `φ` of `2 × 2` matrices on `[0, 1]` with `φ(0) = Id`, `det φ(1) = 1`
and a continuous polar angle `α`: if `tr φ(1) > 2` and `|α(1) - 2πk| < π/2`, then
`czIndexOfPath φ = 2k`; if `tr φ(1) < 2` and `α(1) ∈ (2πk, 2πk + 2π)`, then
`czIndexOfPath φ = 2k + 1`. -/
theorem czIndexOfPath_eq_of_polarAngleLift (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ContinuousOn (fun t i j => φ t i j) (Set.Icc 0 1)) (h0 : φ 0 = 1)
    (hdet : (φ 1).det = 1) (α : ℝ → ℝ) (hα : IsPolarAngleLift φ α) (k : ℤ) :
    (2 < (φ 1).trace → |α 1 - 2 * Real.pi * k| < Real.pi / 2 → czIndexOfPath φ = 2 * k) ∧
    ((φ 1).trace < 2 → 2 * Real.pi * k < α 1 → α 1 < 2 * Real.pi * k + 2 * Real.pi →
      czIndexOfPath φ = 2 * k + 1) := by
  sorry

end HryniewiczCriterion
