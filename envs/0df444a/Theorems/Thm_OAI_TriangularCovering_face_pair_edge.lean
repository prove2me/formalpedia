-- Prove2me | Theorems.Thm_OAI_TriangularCovering_face_pair_edge
-- name    : OAI.TriangularCovering.face_pair_edge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:55:14.50282+00:00
-- url     : https://prove2.me/theorems/ee47b11c-546f-4ace-8aa1-79035b71369c
-- title:
--   Two distinct faces of the tetrahedron $K$ meet inside a line segment
-- statement:
--   Let $H=\sqrt2$, let $K=\{(x,y,Ht):\ x,y,t\in\mathbb{R},\ 0\le t\le 1,\ |x|\le 1-t,\ |y|\le t\}\subset\mathbb{R}^3$ be the regular tetrahedron with vertices $(\pm1,0,0)$ and $(0,\pm1,H)$, and let $F_i=\{p\in K:\ \langle n_i,p\rangle=b_i\}$, $i\in\{0,1,2,3\}$, be its faces, where $n_0=(H,0,1)$, $n_1=(-H,0,1)$, $n_2=(0,H,-1)$, $n_3=(0,-H,-1)$ and $b_0=b_1=H$, $b_2=b_3=0$. For points $a,b\in\mathbb{R}^3$ write $[a,b]=\operatorname{conv}\{a,b\}=\{(1-\lambda)a+\lambda b:\ 0\le\lambda\le 1\}$ for the closed segment joining them. Then for all $i,j\in\{0,1,2,3\}$ with $i\ne j$ there exist points $a,b\in\mathbb{R}^3$ such that
--
--   $$
--   F_i\cap F_j\subseteq[a,b].
--   $$
--
--   Geometrically, two distinct faces of a tetrahedron meet along their common edge; the statement records only the containment in some segment, which is what is needed later. A segment is a degenerate triangle, so its image under any orthogonal projection onto a plane has zero area. Consequently the shadows of two different faces of $K$ overlap only in a set of area zero, which is what allows the area of the shadow of $K$ to be computed as a sum of areas of shadows of faces.
--
--   **Formalization Note** The segment is written as the degenerate triangle `triangle a b b`, the convex hull of the three points $a,b,b$, so that the triangle-area formulas of the development apply to it directly. The faces are `face i` for `i : Fin 4`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Shadows.lean#L143-L190

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

theorem OAI.TriangularCovering.face_pair_edge {i j : Fin 4} (hij : i ≠ j) :
    ∃ a b : Space, face i ∩ face j ⊆ triangle a b b := by sorry
