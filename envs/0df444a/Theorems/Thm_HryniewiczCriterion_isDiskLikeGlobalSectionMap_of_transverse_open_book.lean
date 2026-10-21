-- Prove2me | Theorems.Thm_HryniewiczCriterion_isDiskLikeGlobalSectionMap_of_transverse_open_book
-- name    : HryniewiczCriterion.isDiskLikeGlobalSectionMap_of_transverse_open_book
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T16:53:07.29366+00:00
-- url     : https://prove2.me/theorems/f4036d19-4373-43ea-bcc0-854a83da148c
-- title:
--   The pages of a transverse disk open book whose binding has Conley–Zehnder index $\ge3$ are disk-like global surfaces of section
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $P=(x,T)$ be a periodic orbit on $S$ with $\mu_{CZ}(P)\ge3$. Let $(\mathrm{page}_\theta)_{\theta\in\mathbb{R}}$ be a transverse disk open book on $S$ with binding $P$. Then every page $\mathrm{page}_\theta(\bar{\mathbb D})$ is a disk-like global surface of section bounded by $P$ (`IsDiskLikeGlobalSectionMap`): every trajectory of $X_H$ on $S$ not contained in $x(\mathbb{R})$ meets $\mathrm{page}_\theta(\bar{\mathbb D})$ at arbitrarily large positive and arbitrarily large negative times.
--
--   A *transverse disk open book* on $S=H^{-1}(1)$ with binding $P=(x,T)$ is a family of maps $\mathrm{page}_\theta:\mathbb{R}^2\to\mathbb{R}^4$, $\theta\in\mathbb{R}$, such that
--
--   - $(\theta,u)\mapsto\mathrm{page}_\theta(u)$ is $C^\infty$ and $1$-periodic in $\theta$;
--   - each $\mathrm{page}_\theta$ restricts to a smooth embedding of the closed unit disk $\bar{\mathbb D}$ into $S$ (`IsSmoothDiskEmbedding`, injective differential up to the boundary);
--   - the boundary circle runs along $P$: $\mathrm{page}_\theta(\cos2\pi t,\sin2\pi t)=x(Tt)$;
--   - $X_H$ is transverse to every page in the interior: $X_H(\mathrm{page}_\theta(u))\notin\operatorname{im}D\mathrm{page}_\theta(u)$ for $|u|<1$;
--   - $(\theta,u)\mapsto\mathrm{page}_\theta(u)$ maps $[0,1)\times\mathbb D$ bijectively onto $S\setminus x(\mathbb{R})$, with injective differential at every $(\theta,u)$, $|u|<1$.
--
--   This is an adapted open book decomposition (`AdaptedDiskOpenBook`) without the requirement that the pages be global surfaces of section and without the orientation condition on the pages.
--
--   $\mu_{CZ}(P)\ge3$ means `3 ≤ czIndexOfPath (linearizedXiPath H P Y)` for every linearized flow $Y$ of $X_H$ along $x$ (the linearized flow on $\xi$ in the global frame $(Z_1,Z_2)$, with the lower semicontinuous extension of the index to degenerate orbits). No non-degeneracy is assumed. The statement turns a transverse disk open book whose binding has index at least $3$ into a family of disk-like global surfaces of section with common boundary $P$.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Theorem 3.11 (p. 25); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) 197-289, Theorem 2.5.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.isDiskLikeGlobalSectionMap_of_transverse_open_book (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (hcz : ∀ Y : ℝ → (R4 →L[ℝ] R4), IsLinearizedFlow H P.x Y →
      3 ≤ czIndexOfPath (linearizedXiPath H P Y))
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
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))) :
    ∀ θ : ℝ, IsDiskLikeGlobalSectionMap H P (page θ) := by sorry
