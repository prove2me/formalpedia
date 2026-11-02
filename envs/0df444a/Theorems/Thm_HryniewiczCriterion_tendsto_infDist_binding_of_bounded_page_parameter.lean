-- Prove2me | Theorems.Thm_HryniewiczCriterion_tendsto_infDist_binding_of_bounded_page_parameter
-- name    : HryniewiczCriterion.tendsto_infDist_binding_of_bounded_page_parameter
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:30:14.973905+00:00
-- url     : https://prove2.me/theorems/9e004165-b2d0-4556-a2e1-17828e1524d0
-- title:
--   A trajectory whose page parameter stays bounded on a half-line converges to the binding
-- statement:
--   Let $y$ be a trajectory of $X_H$ on $S$ with a page parameter $(\Theta,u)$, $\Theta$ continuous and strictly monotone. If $\Theta$ is bounded on $[a,\infty)$ for some $a$, then $\operatorname{dist}(y(t),x(\mathbb{R}))\to0$ as $t\to+\infty$. If $\Theta$ is bounded on $(-\infty,a]$ for some $a$, then $\operatorname{dist}(y(t),x(\mathbb{R}))\to0$ as $t\to-\infty$.
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
--   A *page parameter* along a trajectory $y$ of $X_H$ on $S$ is a pair of functions $\Theta:\mathbb{R}\to\mathbb{R}$, $u:\mathbb{R}\to\mathbb D$ (open unit disk) with $y(t)=\mathrm{page}_{\Theta(t)}(u(t))$ for all $t$. Distances to the binding are $\operatorname{dist}(y(t),x(\mathbb{R}))$ (`Metric.infDist`, for the sup norm on $\mathbb{R}^4$; any norm gives the same convergence).
--
--   Role: a trajectory that crosses only finitely many pages in forward (or backward) time accumulates only on the binding. No index hypothesis on $P$ is needed.
-- source:
--   cf. U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Theorem 3.11 (p. 25); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) 197-289, Theorem 2.5.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.MonotoneConvergence

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.tendsto_infDist_binding_of_bounded_page_parameter (H : R4 → ℝ)
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
    (y : ℝ → R4) (hy : IsTrajectory H y) (Θ : ℝ → ℝ) (u : ℝ → Plane)
    (hΘ : Continuous Θ) (hmono : StrictMono Θ ∨ StrictAnti Θ)
    (hyu : ∀ t, u t ∈ openUnitDisk ∧ page (Θ t) (u t) = y t) :
    (∀ a : ℝ, Bornology.IsBounded (Θ '' Set.Ici a) →
      Filter.Tendsto (fun t => Metric.infDist (y t) P.image) Filter.atTop (nhds 0)) ∧
    (∀ a : ℝ, Bornology.IsBounded (Θ '' Set.Iic a) →
      Filter.Tendsto (fun t => Metric.infDist (y t) P.image) Filter.atBot (nhds 0)) := by sorry
