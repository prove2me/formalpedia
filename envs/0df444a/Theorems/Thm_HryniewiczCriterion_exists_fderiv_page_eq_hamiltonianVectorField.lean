-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_fderiv_page_eq_hamiltonianVectorField
-- name    : HryniewiczCriterion.exists_fderiv_page_eq_hamiltonianVectorField
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T16:14:48.559505+00:00
-- url     : https://prove2.me/theorems/609d31cb-494f-4cb1-b2d0-d014dd9ef51c
-- title:
--   At an interior page point, the Hamiltonian vector field has a nonzero page-parameter component
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level (`IsStrictlyStarShapedLevel H`) and let $(\mathrm{page}_\theta)_{\theta\in\mathbb{R}}$ be a family of disk maps $\mathbb{R}^2\to\mathbb{R}^4$ with
--   - $e(\theta,u)=\mathrm{page}_\theta(u)$ of class $C^\infty$ on $\mathbb{R}\times\mathbb{R}^2$;
--   - $\mathrm{page}_\theta(\bar{\mathbb D})\subseteq S$ for every $\theta$;
--   - $X_H$ transverse to every page in the interior: $X_H(\mathrm{page}_\theta(u))\notin\operatorname{im}D\mathrm{page}_\theta(u)$ for $|u|<1$;
--   - $De(\theta,u)$ injective for every $\theta$ and every $u$ in the open unit disk $\mathbb D$.
--
--   Then for every $\theta_0\in\mathbb{R}$ and $v_0\in\mathbb D$ there is a tangent vector $w=(w_\theta,w_u)\in\mathbb{R}\times\mathbb{R}^2$ with
--   $$De(\theta_0,v_0)\,w=X_H(\mathrm{page}_{\theta_0}(v_0))\quad\text{and}\quad w_\theta\neq0.$$
--
--   Role: at interior points of the pages, the Hamiltonian vector field is tangent to the family $e$ and has a nonzero component in the page-parameter direction; this is the infinitesimal statement that the flow of $X_H$ moves across the pages at nonzero speed.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 3.12

import Definitions.Def_HryniewiczCriterion_GlobalSection

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_fderiv_page_eq_hamiltonianVectorField (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H)
    (page : ℝ → Plane → R4) (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hpS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H)
    (htr : ∀ θ, ∀ u ∈ openUnitDisk,
      hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u))
    (hreg : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
      Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))
    {θ₀ : ℝ} {v₀ : Plane} (hv₀ : v₀ ∈ openUnitDisk) :
    ∃ w : ℝ × Plane, fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ₀, v₀) w =
      hamiltonianVectorField H (page θ₀ v₀) ∧ w.1 ≠ 0 := by sorry
