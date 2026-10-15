-- Prove2me | Theorems.Thm_OAI_TriangularCovering_shadowArea_formula
-- name    : OAI.TriangularCovering.shadowArea_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:56:35.040488+00:00
-- url     : https://prove2.me/theorems/453244f4-9c88-4a83-8ce3-dd33762683c3
-- title:
--   Exact shadow area of the regular tetrahedron: $S(u)=\max(\sqrt2|u_1|,|u_3|)+\max(\sqrt2|u_2|,|u_3|)$
-- statement:
--   Let $H=\sqrt2$ and let $K=\{(x,y,Ht):\ x,y,t\in\mathbb{R},\ 0\le t\le 1,\ |x|\le 1-t,\ |y|\le t\}\subset\mathbb{R}^3$ be the regular tetrahedron with vertices $(\pm1,0,0)$ and $(0,\pm1,\sqrt2)$. For a unit vector $u\in\mathbb{R}^3$ let $\pi_u(z)=z-\langle u,z\rangle\,u$ be the orthogonal projection onto the plane $u^\perp$, and let $S(u)=\mathcal{H}^2\bigl(\pi_u(K)\bigr)$ be the area of the shadow of $K$ in direction $u$, where $\mathcal{H}^2$ is the two-dimensional Hausdorff measure on $\mathbb{R}^3$, normalized so that it coincides with Lebesgue area on planes. Then for every $u=(u_1,u_2,u_3)\in\mathbb{R}^3$ with $\|u\|=1$,
--
--   $$
--   S(u)=\max\bigl(\sqrt2\,|u_1|,\ |u_3|\bigr)+\max\bigl(\sqrt2\,|u_2|,\ |u_3|\bigr).
--   $$
--
--   This closed formula for the shadow area as a function of the direction of projection reduces all questions about orthogonal shadows of $K$ to elementary inequalities. For example, $S(\pm e_1)=S(\pm e_2)=\sqrt2$ (the shadow is a triangle with base $2$ and height $\sqrt2$) and $S(\pm e_3)=2$ (the shadow is a square with diagonals of length $2$). It is the main input for the lower bound $S(u)\ge\sqrt2$ and hence for determining the minimal shadow area of $K$.
--
--   **Formalization Note** In Lean, `shadowArea u` is `area (projection u '' K)`, where `projection u z` is $z-\langle u,z\rangle u$ (defined for every vector $u$, but the theorem assumes $\|u\|=1$) and `area B` is the real number obtained by `toReal` from `Measure.euclideanHausdorffMeasure 2 B`. The coordinates `u 0`, `u 1`, `u 2` are $u_1,u_2,u_3$ above, and $H$ is `Real.sqrt 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Shadows.lean#L250-L270

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

theorem OAI.TriangularCovering.shadowArea_formula {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = max (H*|u 0|) |u 2| + max (H*|u 1|) |u 2| := by sorry
