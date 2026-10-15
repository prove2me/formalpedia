-- Prove2me | Theorems.Thm_OAI_RuledApproximation_projectedCylinder_carrier
-- name    : OAI.RuledApproximation.projectedCylinder_carrier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:41:24.001876+00:00
-- url     : https://prove2.me/theorems/363f1adb-28fd-4011-8716-29d302ad3c00
-- title:
--   Projected cylinders are vertically rescaled oblique auxiliary cylinders
-- statement:
--   Fix $h\in\mathbb{R}$, a vector $g=(g_1,g_2)\in\mathbb{R}^2$ and a set $P\subseteq\mathbb{R}^2$. Put $d_h(g)=(1,\,g_1,\,hg_2)\in\mathbb{R}^3$ and $\iota_h(p)=(0,\,p_1,\,hp_2)$ for $p\in\mathbb{R}^2$. The *projected cylinder* $C_h(g,P)$ is the cylinder in $\mathbb{R}^3$ whose axis is the unit vector $d_h(g)/\|d_h(g)\|$ and whose base is the orthogonal projection of $\iota_h(P)$ onto the plane $d_h(g)^{\perp}$; its *carrier* is the union of the lines parallel to the axis through the points of the base. The *auxiliary cylinder* with cross-section $P$ and direction $g$ is the oblique cylinder
--   $$
--   \mathrm{Aux}(P,g)=\{(s,\ b_1+sg_1,\ b_2+sg_2):\ s\in\mathbb{R},\ b\in P\},
--   $$
--   and $\Phi_h(z_1,z_2,z_3)=(z_1,\,z_2,\,hz_3)$ rescales the third coordinate by $h$.
--
--   The theorem states that, for every $h$, $g$ and $P$ (no further assumption), the carrier of the projected cylinder is the $\Phi_h$-image of the auxiliary cylinder:
--   $$
--   \mathrm{carrier}\,C_h(g,P)=\Phi_h\bigl(\mathrm{Aux}(P,g)\bigr)=\{(s,\ b_1+sg_1,\ h(b_2+sg_2)):\ s\in\mathbb{R},\ b\in P\}.
--   $$
--
--   Thus an oblique cylinder over a planar cross-section, described in unscaled coordinates, becomes after the rescaling $\Phi_h$ a genuine Euclidean cylinder with a perpendicular cross-section. This is how the first of the two coordinate maps in the nilpotent covering statement acts on auxiliary cylinders.
--
--   **Formalization Note** The projected cylinder is `projectedCylinder h g P`, built from `physicalUnit h g` (the normalization of `physicalDirection h g`, which is $d_h(g)$) and from `perpendicularProjection h g` applied to `planeEmbedding h`, which is $\iota_h$; the auxiliary cylinder is `auxiliaryCylinder P g` and $\Phi_h$ is `firstPhysicalMap h`. Lean indexes coordinates from $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Projection.lean#L221-L235

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.projectedCylinder_carrier (h : ℝ) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).carrier = firstPhysicalMap h '' auxiliaryCylinder P g := by sorry
