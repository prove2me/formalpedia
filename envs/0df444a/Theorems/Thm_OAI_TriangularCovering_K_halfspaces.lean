-- Prove2me | Theorems.Thm_OAI_TriangularCovering_K_halfspaces
-- name    : OAI.TriangularCovering.K_halfspaces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:53:01.374719+00:00
-- url     : https://prove2.me/theorems/fd779533-4d36-486f-9610-f037caf415a7
-- title:
--   The tetrahedron $K$ as an intersection of four half-spaces
-- statement:
--   Let $H=\sqrt2$ and let $K\subset\mathbb{R}^3$ be the tetrahedron
--   $$
--   K=\bigl\{(x,\,y,\,Ht)\ :\ x,y,t\in\mathbb{R},\ 0\le t\le 1,\ |x|\le 1-t,\ |y|\le t\bigr\},
--   $$
--   that is, the regular tetrahedron with vertices $(\pm1,0,0)$ and $(0,\pm1,\sqrt2)$. Consider the four vectors $n_0=(H,0,1)$, $n_1=(-H,0,1)$, $n_2=(0,H,-1)$, $n_3=(0,-H,-1)$ and the constants $b_0=b_1=H$, $b_2=b_3=0$. Then a point $p=(p_1,p_2,p_3)\in\mathbb{R}^3$ belongs to $K$ if and only if $\langle n_i,p\rangle\le b_i$ for every $i\in\{0,1,2,3\}$; explicitly,
--
--   $$
--   p\in K\iff\quad Hp_1+p_3\le H,\quad -Hp_1+p_3\le H,\quad Hp_2-p_3\le 0,\quad -Hp_2-p_3\le 0 .
--   $$
--
--   This is the half-space description of $K$: the (non-normalized) vectors $n_i$ are outward normals of the four faces and the $b_i$ are the corresponding support values. It converts the parametric definition of $K$ into a system of four linear inequalities, which immediately gives the convexity of $K$, defines its faces $F_i=\{p\in K:\langle n_i,p\rangle=b_i\}$, and is the basic tool for all later computations with the faces and the orthogonal shadows of $K$.
--
--   **Formalization Note** Points are elements of `EuclideanSpace` over the reals indexed by `Fin 3`; the coordinates `z 0`, `z 1`, `z 2` play the roles of $p_1,p_2,p_3$. The set `K` is defined through the parametrization `point x y t` $=(x,y,Ht)$, and $n_i$, $b_i$ are the `Fin 4`-indexed families `faceNormal` and `faceBound`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Tetrahedron.lean#L25-L41

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

theorem OAI.TriangularCovering.K_halfspaces (z : Space) : z ∈ K ↔ ∀ i, inner ℝ (faceNormal i) z ≤ faceBound i := by sorry
