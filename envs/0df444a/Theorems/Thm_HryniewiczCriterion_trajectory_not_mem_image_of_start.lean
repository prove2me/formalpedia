-- Prove2me | Theorems.Thm_HryniewiczCriterion_trajectory_not_mem_image_of_start
-- name    : HryniewiczCriterion.trajectory_not_mem_image_of_start
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:58:47.035766+00:00
-- url     : https://prove2.me/theorems/655f2460-11e8-4154-977e-88b21e789fc8
-- title:
--   A Hamiltonian trajectory that starts off a periodic orbit never meets it
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ be smooth, let $P=(x,T)$ be a periodic orbit of the Hamiltonian vector field $X_H$, and let $y:\mathbb{R}\to\mathbb{R}^4$ be a trajectory of $X_H$ (defined for all times, on $H^{-1}(1)$). If $y(0)$ does not lie on the image $x(\mathbb{R})$ of $P$, then $y(t)\notin x(\mathbb{R})$ for every $t\in\mathbb{R}$.
--
--   So a trajectory either is a reparametrization of a periodic orbit or stays off it for all times; this is used for trajectories off the binding orbit of an open book.
--
--   **Formalization Note** Trajectories are `IsTrajectory H y` (with `HasDerivAt` for $X_H$ at every time); the image of $P$ is `P.image = Set.range P.x`.
-- source:
--   Standard uniqueness for smooth ODEs; used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 3.12

import Definitions.Def_HryniewiczCriterion_Basic

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.trajectory_not_mem_image_of_start (H : R4 → ℝ) (hH : ContDiff ℝ ∞ H)
    (P : PeriodicOrbit H) (y : ℝ → R4) (hy : IsTrajectory H y) (hy0 : y 0 ∉ P.image) :
    ∀ t, y t ∉ P.image := by sorry
