-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_local_page_branch
-- name    : HryniewiczCriterion.exists_local_page_branch
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T16:07:54.949723+00:00
-- url     : https://prove2.me/theorems/79d5c982-807c-4cfa-b442-031171e2e38a
-- title:
--   Near a point of a transverse page, a trajectory has a local page parameter with non-zero derivative
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level of a smooth $H$, and let $\mathrm{page}:\mathbb{R}\times\mathbb{R}^2\to\mathbb{R}^4$, $(\theta,u)\mapsto\mathrm{page}_\theta(u)$, be smooth with $\mathrm{page}_\theta(\bar{\mathbb{D}})\subseteq S$ for every $\theta$, where $\mathbb{D}$ is the open unit disk. Assume that on $\mathbb{R}\times\mathbb{D}$ the differential of $(\theta,u)\mapsto\mathrm{page}_\theta(u)$ is injective, and that $X_H(\mathrm{page}_\theta(u))$ is not in the image of $D(\mathrm{page}_\theta)(u)$ (the pages are transverse to $X_H$).
--
--   Let $y$ be a trajectory of $X_H$ and suppose $y(t_0)=\mathrm{page}_{\theta_0}(u_0)$ with $u_0\in\mathbb{D}$. Then there are functions $\theta(t)$, $u(t)$ and a real $c\neq0$ such that $\theta(t_0)=\theta_0$, $\theta$ has derivative $c$ at $t_0$, and for all $t$ near $t_0$
--   $$u(t)\in\mathbb{D},\qquad \mathrm{page}_{\theta(t)}(u(t))=y(t).$$
--
--   So near any point where it crosses the interior of a page, a trajectory moves through the family of pages with non-zero speed in the page parameter.
--
--   **Formalization Note** "For all $t$ near $t_0$" is `∀ᶠ t in 𝓝 t₀`; the derivative is `HasDerivAt θ c t₀`; the open and closed unit disks are `openUnitDisk` and `closedUnitDisk`.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 3.12

import Definitions.Def_HryniewiczCriterion_GlobalSection

open HryniewiczCriterion
open scoped ContDiff Topology

theorem HryniewiczCriterion.exists_local_page_branch (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (page : ℝ → Plane → R4) (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hDS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H)
    (htr : ∀ θ, ∀ u ∈ openUnitDisk,
      hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u))
    (hreg : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
      Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))
    (y : ℝ → R4) (hy : IsTrajectory H y) (t₀ θ₀ : ℝ) (u₀ : Plane) (hu₀ : u₀ ∈ openUnitDisk)
    (h0 : page θ₀ u₀ = y t₀) :
    ∃ (θ : ℝ → ℝ) (u : ℝ → Plane) (c : ℝ), c ≠ 0 ∧ HasDerivAt θ c t₀ ∧ θ t₀ = θ₀ ∧
      ∀ᶠ t in 𝓝 t₀, u t ∈ openUnitDisk ∧ page (θ t) (u t) = y t := by sorry
