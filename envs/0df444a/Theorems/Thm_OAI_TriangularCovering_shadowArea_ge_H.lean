-- Prove2me | Theorems.Thm_OAI_TriangularCovering_shadowArea_ge_H
-- name    : OAI.TriangularCovering.shadowArea_ge_H
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:57:47.332577+00:00
-- url     : https://prove2.me/theorems/db2b2a2a-7014-4f67-8c9a-d31e7ac23f35
-- title:
--   Every orthogonal shadow of the regular tetrahedron $K$ has area at least $\sqrt2$
-- statement:
--   Let $H=\sqrt2$ and let $K=\{(x,y,Ht):\ x,y,t\in\mathbb{R},\ 0\le t\le 1,\ |x|\le 1-t,\ |y|\le t\}\subset\mathbb{R}^3$ be the regular tetrahedron with vertices $(\pm1,0,0)$ and $(0,\pm1,\sqrt2)$. For a unit vector $u\in\mathbb{R}^3$ let $\pi_u(z)=z-\langle u,z\rangle\,u$ be the orthogonal projection onto the plane $u^\perp$, and let $S(u)=\mathcal{H}^2\bigl(\pi_u(K)\bigr)$ be the area of the shadow of $K$ in direction $u$, where $\mathcal{H}^2$ is the two-dimensional Hausdorff measure on $\mathbb{R}^3$, normalized so that it coincides with Lebesgue area on planes. Then for every $u\in\mathbb{R}^3$ with $\|u\|=1$,
--
--   $$
--   S(u)\ge\sqrt2 .
--   $$
--
--   In words: every orthogonal projection of the regular tetrahedron with edge length $2$ onto a plane has area at least $\sqrt2$. The bound is sharp, since the exact shadow-area formula gives $S(1,0,0)=\sqrt2$. Consequently the minimal shadow area $A_{\min}=\inf_{\|u\|=1}S(u)$ equals $\sqrt2=H$, and for any unit vector $u$ and any base area $a\ge 0$ one has $a/S(u)\le a/H$, which compares normalized costs of cylinders with direction $u$ to their plain base areas.
--
--   **Formalization Note** In Lean, `shadowArea u` is `area (projection u '' K)`, where `projection u z` is $z-\langle u,z\rangle u$ and `area B` is the real number obtained by `toReal` from `Measure.euclideanHausdorffMeasure 2 B`; the theorem assumes $\|u\|=1$, and $H$ is `Real.sqrt 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Shadows.lean#L272-L290

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
import Definitions.Def_OAI_Geometry_TriangularCovering_Shadows

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.shadowArea_ge_H {u : Space} (hu : ‖u‖ = 1) : H ≤ shadowArea u := by sorry
