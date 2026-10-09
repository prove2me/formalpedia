-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_circlePoint_lift_of_immersion
-- name    : HryniewiczCriterion.exists_circlePoint_lift_of_immersion
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T22:26:45.794317+00:00
-- url     : https://prove2.me/theorems/980fe491-00a8-41f6-a086-a9021623f066
-- title:
--   A periodic immersion of the line into the circle lifts through $\theta\mapsto(\cos2\pi\theta,\sin2\pi\theta)$ with non-zero degree
-- statement:
--   Let $u:\mathbb{R}\to S^1\subset\mathbb{R}^2$ be a $C^2$ map of period $1$ whose derivative never vanishes. Then $u$ has a $C^1$ lift through $\mathrm{circlePoint}(\theta)=(\cos2\pi\theta,\sin2\pi\theta)$:
--   $$u(s)=\big(\cos2\pi\theta(s),\ \sin2\pi\theta(s)\big),\qquad \theta(s+1)=\theta(s)+k,$$
--   with $\theta'$ continuous and a degree $k\in\mathbb{Z}$ that is **non-zero**.
--
--   So a periodic immersion of the line into the circle covers the circle $|k|\ge1$ times. Explicitly $2\pi\theta'=u_0u_1'-u_1u_0'$, which never vanishes, so $\theta$ is strictly monotone and cannot return to its initial value after one period.
-- source:
--   Standard lifting of circle maps (e.g. Hatcher, Algebraic Topology, Prop. 1.30); used for boundary parametrizations in U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 3.12

import Definitions.Def_HryniewiczCriterion_GlobalSection

open HryniewiczCriterion

theorem HryniewiczCriterion.exists_circlePoint_lift_of_immersion (u : ℝ → Plane) (hu : ContDiff ℝ 2 u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hu' : ∀ s, deriv u s ≠ 0) :
    ∃ (θ θ' : ℝ → ℝ) (k : ℤ), k ≠ 0 ∧ Continuous θ' ∧ (∀ s, HasDerivAt θ (θ' s) s) ∧
      (∀ s, θ (s + 1) = θ s + k) ∧ ∀ s, u s = circlePoint (θ s) := by sorry
