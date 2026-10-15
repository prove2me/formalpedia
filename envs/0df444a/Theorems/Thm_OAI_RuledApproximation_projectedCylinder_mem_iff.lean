-- Prove2me | Theorems.Thm_OAI_RuledApproximation_projectedCylinder_mem_iff
-- name    : OAI.RuledApproximation.projectedCylinder_mem_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:40:42.939298+00:00
-- url     : https://prove2.me/theorems/98c04c02-6d2e-4d87-b664-0103a0171a75
-- title:
--   Membership in a projected cylinder: lines in the physical direction through the embedded tile
-- statement:
--   Work in $\mathbb{R}^2$ and $\mathbb{R}^3$ with their Euclidean structures. Fix $h\in\mathbb{R}$ and $g=(g_1,g_2)\in\mathbb{R}^2$, and set:
--
--   - $E_h(p)=(0,\ p_1,\ h\,p_2)$ for $p\in\mathbb{R}^2$, the physical embedding of the parameter plane;
--   - $d_{h,g}=(1,\ g_1,\ h\,g_2)$, which is nonzero, and the unit axis $u_{h,g}=d_{h,g}/\|d_{h,g}\|$;
--   - $\pi_{h,g}(p)=E_h(p)-\dfrac{\langle d_{h,g},E_h(p)\rangle}{\|d_{h,g}\|^2}\,d_{h,g}$, the orthogonal projection of $E_h(p)$ onto the plane $u_{h,g}^{\perp}$.
--
--   For $P\subseteq\mathbb{R}^2$, the projected cylinder $\mathcal{C}_{h,g}(P)$ has axis $u_{h,g}$ and base $\pi_{h,g}(P)$, so its carrier is $\{\pi_{h,g}(p)+t\,u_{h,g}:\ p\in P,\ t\in\mathbb{R}\}$.
--
--   **Theorem.** For every $h\in\mathbb{R}$, $g\in\mathbb{R}^2$, every set $P\subseteq\mathbb{R}^2$ and every $x\in\mathbb{R}^3$,
--   $$x\in\operatorname{carrier}\,\mathcal{C}_{h,g}(P)\iff \exists\,p\in P,\ \exists\,s\in\mathbb{R}:\quad x=E_h(p)+s\,d_{h,g}.$$
--   In other words, the carrier is $E_h(P)+\mathbb{R}\,d_{h,g}$, the union of the lines with direction $d_{h,g}$ through the points of the oblique planar copy $E_h(P)$.
--
--   This is the practical membership test for the cylinders used in the covering constructions, since it avoids computing orthogonal projections. For instance, the point $(s,\ p_1+s\,v_1(p),\ h(p_2+s\,v_2(p)))$ of a physically normalized ruled set equals $E_h\bigl(p+s(v(p)-g)\bigr)+s\,d_{h,g}$, so it lies in $\mathcal{C}_{h,g}(P)$ whenever $p+s(v(p)-g)\in P$. The same description identifies the carrier with the image of the auxiliary cylinder $\{(s,\ b+s\,g):\ s\in\mathbb{R},\ b\in P\}$ under $(z_1,z_2,z_3)\mapsto(z_1,z_2,hz_3)$, and gives the carriers of the triangular tip cylinders.
--
--   **Formalization Note** The objects are `planeEmbedding h`, `physicalDirection h g`, `projectedCylinder h g P` and `Cylinder.carrier`. The statement holds for every real $h$, including $h=0$, where $E_0$ is degenerate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Projection.lean#L195-L219

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.projectedCylinder_mem_iff (h : ℝ) (g : Plane) (P : Set Plane) (x : Space) :
    x ∈ (projectedCylinder h g P).carrier ↔
      ∃ p ∈ P, ∃ s : ℝ, x = planeEmbedding h p + s • physicalDirection h g := by sorry
