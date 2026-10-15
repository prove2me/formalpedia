-- Prove2me | Theorems.Thm_OAI_CompactBanach_norm_map_point_sub_le
-- name    : OAI.CompactBanach.norm_map_point_sub_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:05:50.000267+00:00
-- url     : https://prove2.me/theorems/976c9824-ae84-418e-9c49-dd478050f3c6
-- title:
--   A linear map that does not expand coordinate vectors moves differences of strip points by at most $6R$
-- statement:
--   Work in real $\ell^2=\ell^2(\mathbb{N};\mathbb{R})$ with standard unit vectors $e_0,e_1,e_2,\dots$. Recall the strip construction: level $j\in\mathbb{N}$ has scale $r_j=1000^{-(j+1)}$, the coordinate index of level $j$ and color $i$ is $c(j,i)=2+\pi(j,i)$, where $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is a fixed pairing bijection, and a base point $p=(p_1,p_2)\in\mathbb{R}^2$ together with a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$ gives the point
--   $$
--   z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0} r_j\,e_{c(j,\,w_j-1)}\in\ell^2 .
--   $$
--
--   **Theorem.** Let $B$ be a real normed space and $T:\ell^2\to B$ a real-linear map (not assumed continuous) such that $\|T(a\,e_i)\|\le|a|$ for all $i\in\mathbb{N}$ and $a\in\mathbb{R}$, that is, $\|Te_i\|\le1$ for every $i$. Let $p,q\in\mathbb{R}^2$, let $w,w'$ be finitely supported tuples, and let $R\ge0$ satisfy
--   $$
--   |p_1-q_1|\le R,\qquad |p_2-q_2|\le R,\qquad r_j\le R\ \text{ for every level } j \text{ with } w_j\neq w'_j .
--   $$
--   Then
--   $$
--   \bigl\|T\bigl(z(p,w)-z(q,w')\bigr)\bigr\|\le 6R .
--   $$
--   No admissibility of $(p,w)$ or $(q,w')$ is required.
--
--   The bound only sees the coordinates in which the two points differ and the rapid decay of the scales, so it holds for every linear map that does not expand individual coordinate vectors. With $T$ the identity of $\ell^2$ it bounds distances between strip points in terms of their coordinate differences, and with $T$ a coordinate map into another normed space it gives the upper Lipschitz bound for linear placements of finite pieces of the strip set.
--
--   **Formalization Note** The points are `point p w` with `p q : Base = ℝ × ℝ` and `w w' : Tuple = ℕ →₀ ℕ`, $r_j$ is `scale j`, and $a\,e_i$ is `lp.single 2 i a`. The map $T$ is a `LinearMap` from `RealL2` to `B`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/SparseCoordinates.lean#L47-L89

import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

open OAI OAI.CompactBanach
open Set Metric
open DoublingHilbert

theorem OAI.CompactBanach.norm_map_point_sub_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : RealL2 →ₗ[ℝ] B) (hT : ∀ i a, ‖T (lp.single 2 i a)‖ ≤ |a|)
    (p q : Base) (w w' : Tuple) {R : ℝ} (hR : 0 ≤ R)
    (hf : |p.1 - q.1| ≤ R) (hs : |p.2 - q.2| ≤ R)
    (hw : ∀ j, w j ≠ w' j → scale j ≤ R) :
    ‖T (point p w - point q w')‖ ≤ 6 * R := by sorry
