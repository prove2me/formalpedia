-- Prove2me | Theorems.Thm_HryniewiczCriterion_graphBasis4_det_mul_ratio_mem_slitPlane
-- name    : HryniewiczCriterion.graphBasis4_det_mul_ratio_mem_slitPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:03:12.029772+00:00
-- url     : https://prove2.me/theorems/ecece2aa-c665-48ed-89ee-5d08adb1b6f9
-- title:
--   The graph determinant is multiplicative on $Sp(4)$ up to a factor in the slit plane
-- statement:
--   Let $g_1,g_2$ be real $4\times4$ matrices preserving the standard symplectic form $\omega_0$, and let $\delta(g)=\det(\texttt{graphBasis4}\ g)$ be the graph determinant. Then $\delta(g_1)\neq0$, $\delta(g_2)\neq0$, and
--   $$\frac{4\,\delta(g_1g_2)}{\delta(g_1)\,\delta(g_2)}\in\mathbb{C}\setminus(-\infty,0].$$
--
--   So $\delta$ is multiplicative on the symplectic group up to a factor that never meets the negative real axis. Along continuous paths of symplectic matrices, the principal argument of this factor is therefore continuous. This is the quasimorphism property of the Maslov rotation function, and it lets one compare determinant angles of products of symplectic paths without a homotopy argument.
-- source:
--   Standard estimate behind the quasimorphism property of the Maslov rotation function on the symplectic group (cf. McDuff–Salamon, Introduction to Symplectic Topology, Section 2.2); stated and proved here in the coordinates of `graphBasis4`. Used for the determinant angle in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, Theorem 3.4, pp. 219–222.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.graphBasis4_det_mul_ratio_mem_slitPlane (g₁ g₂ : Matrix (Fin 4) (Fin 4) ℝ)
    (h₁ : ∀ u v : R4, omega0 (g₁.mulVec u) (g₁.mulVec v) = omega0 u v)
    (h₂ : ∀ u v : R4, omega0 (g₂.mulVec u) (g₂.mulVec v) = omega0 u v) :
    (graphBasis4 g₁).det ≠ 0 ∧ (graphBasis4 g₂).det ≠ 0 ∧
      4 * (graphBasis4 (g₁ * g₂)).det / ((graphBasis4 g₁).det * (graphBasis4 g₂).det) ∈
        Complex.slitPlane := by sorry
