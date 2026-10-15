-- Prove2me | Theorems.Thm_OAI_TriangularCovering_face_eq_triangle
-- name    : OAI.TriangularCovering.face_eq_triangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:53:29.763128+00:00
-- url     : https://prove2.me/theorems/badfe7bd-f239-48e2-871e-673bf213de4a
-- title:
--   Each face of the tetrahedron $K$ is the triangle spanned by its three vertices
-- statement:
--   Let $H=\sqrt2$ and let $K=\{(x,y,Ht):\ x,y,t\in\mathbb{R},\ 0\le t\le 1,\ |x|\le 1-t,\ |y|\le t\}\subset\mathbb{R}^3$ be the regular tetrahedron with vertices $(\pm1,0,0)$ and $(0,\pm1,H)$. With $n_0=(H,0,1)$, $n_1=(-H,0,1)$, $n_2=(0,H,-1)$, $n_3=(0,-H,-1)$ and $b_0=b_1=H$, $b_2=b_3=0$, the faces of $K$ are the sets $F_i=\{p\in K:\ \langle n_i,p\rangle=b_i\}$ for $i\in\{0,1,2,3\}$. Write $\operatorname{conv}\{a,b,c\}$ for the convex hull of three points, i.e. the closed triangle with these vertices. Then every face is the triangle spanned by three vertices of $K$:
--
--   $$
--   \begin{aligned}
--   F_0&=\operatorname{conv}\{(1,0,0),\,(0,1,H),\,(0,-1,H)\},\\
--   F_1&=\operatorname{conv}\{(-1,0,0),\,(0,1,H),\,(0,-1,H)\},\\
--   F_2&=\operatorname{conv}\{(0,1,H),\,(1,0,0),\,(-1,0,0)\},\\
--   F_3&=\operatorname{conv}\{(0,-1,H),\,(1,0,0),\,(-1,0,0)\}.
--   \end{aligned}
--   $$
--
--   Identifying each face, defined implicitly by a supporting hyperplane, with an explicit triangle makes triangle formulas available. In particular, the area of the orthogonal projection of a face onto a plane can then be computed from the cross product of two edge vectors, which is the starting point of the exact formula for the shadow areas of $K$.
--
--   **Formalization Note** In Lean the face is `face i`, the set of points of `K` on which the inner product with `faceNormal i` equals `faceBound i`, and `triangle a b c` is the convex hull of the range of the vector `![a, b, c]`. The three vertices are `faceVertices i 0`, `faceVertices i 1`, `faceVertices i 2`, listed above in this order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Tetrahedron.lean#L63-L106

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.face_eq_triangle (i : Fin 4) :
    face i = triangle (faceVertices i 0) (faceVertices i 1) (faceVertices i 2) := by sorry
