-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_page_parameter_along_trajectory
-- name    : HryniewiczCriterion.exists_page_parameter_along_trajectory
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:29:40.400724+00:00
-- url     : https://prove2.me/theorems/a9af591d-eb0e-4680-992b-1e86144e04de
-- title:
--   Along a trajectory off the binding of a transverse disk open book, the page parameter is continuous and strictly monotone
-- statement:
--   Let $y$ be a trajectory of $X_H$ on $S$ with $y(0)\notin x(\mathbb{R})$. Then $y$ has a page parameter $(\Theta,u)$ with $\Theta$ continuous and strictly monotone (strictly increasing or strictly decreasing): $u(t)$ lies in the open unit disk and $y(t)=\mathrm{page}_{\Theta(t)}(u(t))$ for every $t\in\mathbb{R}$.
--
--   Here $S=H^{-1}(1)\subset\mathbb{R}^4$ is a strictly star-shaped level, $P=(x,T)$ is a periodic orbit on $S$, and $(\mathrm{page}_\theta)_{\theta\in\mathbb{R}}$ is a *transverse disk open book* on $S$ with binding $P$:
--   - $(\theta,u)\mapsto\mathrm{page}_\theta(u)$ is $C^\infty$ and $1$-periodic in $\theta$;
--   - each $\mathrm{page}_\theta$ restricts to a smooth embedding of the closed unit disk $\bar{\mathbb D}$ into $S$ (`IsSmoothDiskEmbedding`);
--   - the boundary circle runs along $P$: $\mathrm{page}_\theta(\cos2\pi t,\sin2\pi t)=x(Tt)$;
--   - $X_H$ is transverse to every page in the interior: $X_H(\mathrm{page}_\theta(u))\notin\operatorname{im}D\mathrm{page}_\theta(u)$ for $|u|<1$;
--   - $(\theta,u)\mapsto\mathrm{page}_\theta(u)$ maps $[0,1)\times\mathbb D$ bijectively onto $S\setminus x(\mathbb{R})$, with injective differential at every $(\theta,u)$, $|u|<1$.
--
--   These are exactly the open book hypotheses of `isDiskLikeGlobalSectionMap_of_transverse_open_book`.
--
--   A *page parameter* along a trajectory $y$ of $X_H$ on $S$ is a pair of functions $\Theta:\mathbb{R}\to\mathbb{R}$, $u:\mathbb{R}\to\mathbb D$ (open unit disk) with $y(t)=\mathrm{page}_{\Theta(t)}(u(t))$ for all $t$.
--
--   Role: $\Theta$ is a real-valued lift, along the trajectory, of the angular coordinate $S\setminus x(\mathbb{R})\to\mathbb{R}/\mathbb{Z}$ of the open book. No index hypothesis on $P$ is needed.
-- source:
--   cf. U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Theorem 3.11 (p. 25); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) 197-289, Theorem 2.5.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.MonotoneConvergence

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_page_parameter_along_trajectory (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (page : ℝ → Plane → R4)
    (hob : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2) ∧
      (∀ θ u, page (θ + 1) u = page θ u) ∧
      (∀ θ, IsSmoothDiskEmbedding (page θ)) ∧
      (∀ θ, page θ '' closedUnitDisk ⊆ energySurface H) ∧
      (∀ θ t, page θ (circlePoint t) = P.x (P.T * t)) ∧
      (∀ θ, ∀ u ∈ openUnitDisk,
        hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u)) ∧
      (∀ y ∈ energySurface H, y ∉ P.image →
        ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y) ∧
      (∀ θ : ℝ, ∀ u ∈ openUnitDisk,
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u))))
    (y : ℝ → R4) (hy : IsTrajectory H y) (hy0 : y 0 ∉ P.image) :
    ∃ (Θ : ℝ → ℝ) (u : ℝ → Plane), Continuous Θ ∧ (StrictMono Θ ∨ StrictAnti Θ) ∧
      ∀ t, u t ∈ openUnitDisk ∧ page (Θ t) (u t) = y t := by sorry
