-- Prove2me | Theorems.Thm_HryniewiczCriterion_ambient_positive_czIndex_ge_three
-- name    : HryniewiczCriterion.ambient_positive_czIndex_ge_three
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T22:16:20.737977+00:00
-- url     : https://prove2.me/theorems/1e547071-350f-4261-83d2-e2c6af72f805
-- title:
--   HWZ index bound for an ambient positive-definite defining Hamiltonian
-- statement:
--   Let $H$ be smooth and let its unit level be strictly star-shaped. Assume the Hessian of $H$ is positive definite on all ambient vectors at every point of that level. For every periodic Hamiltonian orbit, including iterates, and every normalized variational flow, the lower semicontinuous Conley–Zehnder index of the induced contact-plane path in the global frame is at least $3$.
--
--   This is the positive ambient Hessian case of the HWZ dynamical-convexity estimate; it does not assume a winding bound. Degenerate periodic orbits use the lower semicontinuous endpoint convention.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), Theorem 3.4, https://doi.org/10.2307/120994; stronger ambient Hessian hypothesis. Index convention: Hryniewicz, https://arxiv.org/html/1105.2077v5, Definition 1.1 and Section 2.1.1, equations (4)–(5).

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.ambient_positive_czIndex_ge_three
    (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) x v v)
    (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4))
    (hY : IsLinearizedFlow H P.x Y) :
    3 ≤ czIndexOfPath (linearizedXiPath H P Y) := by sorry
