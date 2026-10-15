-- Prove2me | Theorems.Thm_OAI_CompactBanach_finite_coordinate_support
-- name    : OAI.CompactBanach.finite_coordinate_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:06:27.060271+00:00
-- url     : https://prove2.me/theorems/0eabf911-bc38-40f4-a5cd-c41c0d7dd500
-- title:
--   Finitely many points of the strip set are supported on finitely many coordinates
-- statement:
--   Let $S\subseteq\ell^2$ be the strip set: the set of all points
--   $$
--   z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0} r_j\,e_{2+\pi(j,\,w_j-1)}
--   $$
--   for admissible pairs $(p,w)$ of a base point $p=(p_1,p_2)\in\mathbb{R}^2$ and a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$, with the metric of real $\ell^2$. Here $e_0,e_1,\dots$ are the standard unit vectors of $\ell^2$, $r_j=1000^{-(j+1)}$, and $\pi$ is a pairing bijection of $\mathbb{N}\times\mathbb{N}$ onto $\mathbb{N}$; admissibility (a colored-strip condition on $p$ at each level where $w_j\neq0$) plays no role below.
--
--   **Theorem.** For every finite set $X\subseteq S$ there is a finite set $I\subseteq\mathbb{N}$ such that
--   $$
--   z_i=0\qquad\text{for all } z\in X \text{ and all } i\in\mathbb{N}\setminus I ,
--   $$
--   where $z_i$ denotes the $i$-th coordinate of $z\in\ell^2$.
--
--   Thus every finite configuration of points of $S$ lies in the finite-dimensional coordinate subspace spanned by $\{e_i: i\in I\}$. This is what allows a finite piece of $S$ to be mapped linearly into an arbitrary infinite-dimensional normed space by assigning one vector to each coordinate in $I$.
--
--   **Formalization Note** $S$ is `constructedSet`, $X$ is a `Finset RealL2` all of whose elements are assumed to lie in `constructedSet`, and $z_i$ is `z i` for `z : RealL2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/CoordinateSupport.lean#L69-L85

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

open OAI OAI.CompactBanach
open Set Metric
open DoublingHilbert

theorem OAI.CompactBanach.finite_coordinate_support (X : Finset RealL2)
    (hX : ∀ z ∈ X, z ∈ constructedSet) :
    ∃ I : Finset ℕ, ∀ z ∈ X, ∀ i ∉ I, z i = 0 := by sorry
