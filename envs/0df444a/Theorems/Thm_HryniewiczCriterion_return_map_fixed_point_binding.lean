-- Prove2me | Theorems.Thm_HryniewiczCriterion_return_map_fixed_point_binding
-- name    : HryniewiczCriterion.return_map_fixed_point_binding
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T21:19:06.419531+00:00
-- url     : https://prove2.me/theorems/f3aa9325-2914-4b85-b5e2-7260e66ab934
-- title:
--   Theorem 1.8: orbits through fixed points of the return map bind new open books
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped energy surface whose flow is dynamically convex. Let $D_0$ be any disk-like global surface of section, bounded by a periodic orbit $P_0$. Let $P_1=(x_1,T_1)$ be a periodic orbit through a fixed point of the first return map of $D_0\setminus\partial D_0$. That is, $x_1(0)$ lies in the interior of $D_0$, and $x_1(t)\notin D_0$ for $0<t<T_1$. Then
--
--   1. $P_1$ is unknotted;
--   2. $\operatorname{sl}(P_1)=-1$;
--   3. $P_1$ is the binding of an adapted open book decomposition of $S$ with disk-like pages.
--
--   By Brouwer's translation theorem the return map of the Hofer–Wysocki–Zehnder disk has a fixed point. So the flow has at least two geometrically distinct systems of disk-like global sections.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Theorem 1.8, p. 3 (proved in Section 4; Proposition 4.1)

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

namespace HryniewiczCriterion

/-- Hryniewicz, Theorem 1.8: let `D₀` be a disk-like global surface of section of a
dynamically convex flow. A periodic orbit `P₁` through a fixed point of the first
return map of `D₀ \ ∂D₀` is unknotted, has `sl(P₁) = -1`, and binds an adapted open
book decomposition with disk-like pages. -/
theorem return_map_fixed_point_binding (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P₀ : PeriodicOrbit H) (e₀ : Plane → R4) (hD₀ : IsDiskLikeGlobalSectionMap H P₀ e₀)
    (P₁ : PeriodicOrbit H) (hfix : P₁.x 0 ∈ e₀ '' openUnitDisk)
    (hfirst : ∀ t : ℝ, 0 < t → t < P₁.T → P₁.x t ∉ e₀ '' closedUnitDisk) :
    IsUnknotted H P₁ ∧ HasSelfLinkingNumber H P₁ (-1) ∧ HasAdaptedDiskOpenBook H P₁ := by sorry

end HryniewiczCriterion
