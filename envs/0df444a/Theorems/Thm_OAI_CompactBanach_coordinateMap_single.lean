-- Prove2me | Theorems.Thm_OAI_CompactBanach_coordinateMap_single
-- name    : OAI.CompactBanach.coordinateMap_single
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:07:27.269423+00:00
-- url     : https://prove2.me/theorems/bb1bdaee-057d-43ed-8678-040f20e7f63b
-- title:
--   A coordinate map built from vectors of norm at most one does not expand coordinate vectors
-- statement:
--   Let $B$ be a real normed space, $I\subseteq\mathbb{N}$ a finite set, and $(v_i)_{i\in I}$ vectors of $B$ with $\|v_i\|\le1$ for every $i\in I$. Let $T_{I,v}:\ell^2\to B$ be the coordinate map $T_{I,v}(z)=\sum_{i\in I}z_i\,v_i$, where $z_i$ is the $i$-th coordinate of $z$ in real $\ell^2$, and let $e_0,e_1,\dots$ be the standard unit vectors of $\ell^2$.
--
--   **Theorem.** For every index $j\in\mathbb{N}$ and every $a\in\mathbb{R}$,
--   $$
--   \|T_{I,v}(a\,e_j)\|\le|a| .
--   $$
--
--   Thus a coordinate map assembled from vectors of the closed unit ball satisfies $\|T_{I,v}e_j\|\le1$ for all $j$, which is exactly the hypothesis under which linear images of differences of strip points are bounded by six times the coordinate differences; it yields the upper half of the bi-Lipschitz estimate for linear placements of finite pieces of the strip set.
--
--   **Formalization Note** The map is `coordinateMap I v`, the vector $a\,e_j$ is `lp.single 2 j a`, and `v : I → B` is indexed by the elements of the finset `I`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/CoordinateMap.lean#L19-L42

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
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap

open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators
open DoublingHilbert

theorem OAI.CompactBanach.coordinateMap_single {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (I : Finset ℕ) (v : I → B) (hv : ∀ i, ‖v i‖ ≤ 1) (j : ℕ) (a : ℝ) :
    ‖coordinateMap I v (lp.single 2 j a)‖ ≤ |a| := by sorry
