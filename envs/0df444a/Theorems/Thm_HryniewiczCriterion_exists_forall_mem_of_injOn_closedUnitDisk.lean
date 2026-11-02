-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_forall_mem_of_injOn_closedUnitDisk
-- name    : HryniewiczCriterion.exists_forall_mem_of_injOn_closedUnitDisk
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T16:14:44.732406+00:00
-- url     : https://prove2.me/theorems/4131eb61-0462-47b5-88cc-eaea49e27d32
-- title:
--   For a continuous family of maps injective on the closed disk, nearby parameters and nearby image points force nearby disk points
-- statement:
--   Let $(f_\theta)_{\theta\in\mathbb{R}}$, $f_\theta:\mathbb{R}^2\to\mathbb{R}^4$, be a family with $(\theta,v)\mapsto f_\theta(v)$ jointly continuous, let $\theta_0\in\mathbb{R}$, and assume $f_{\theta_0}$ is injective on the closed unit disk $\bar{\mathbb D}$. Let $v_0\in\bar{\mathbb D}$ and let $U$ be a neighborhood of $(\theta_0,v_0)$ in $\mathbb{R}\times\mathbb{R}^2$. Then there is $\eta>0$ such that for all $\theta\in\mathbb{R}$ and $v\in\bar{\mathbb D}$,
--   $$|\theta-\theta_0|<\eta\ \text{ and }\ \|f_\theta(v)-f_{\theta_0}(v_0)\|<\eta \implies (\theta,v)\in U.$$
--
--   Norms are the default sup norms on `Fin 2 → ℝ` and `Fin 4 → ℝ`.
--
--   Role: for a family of disk maps such as the pages of an open book, the disk coordinate of a point lying on a page with nearby parameter is close to the disk coordinate of a nearby point of the page $f_{\theta_0}$, uniformly over the closed disk.
-- source:
--   Standard compactness argument; used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 3.12

import Definitions.Def_HryniewiczCriterion_GlobalSection

open HryniewiczCriterion

theorem HryniewiczCriterion.exists_forall_mem_of_injOn_closedUnitDisk {f : ℝ → Plane → R4}
    (hf : Continuous (fun z : ℝ × Plane => f z.1 z.2))
    {θ₀ : ℝ} {v₀ : Plane} (hinj : Set.InjOn (f θ₀) closedUnitDisk) (hv₀ : v₀ ∈ closedUnitDisk)
    {U : Set (ℝ × Plane)} (hU : U ∈ nhds (θ₀, v₀)) :
    ∃ η > 0, ∀ θ v, |θ - θ₀| < η → v ∈ closedUnitDisk → ‖f θ v - f θ₀ v₀‖ < η →
      (θ, v) ∈ U := by sorry
