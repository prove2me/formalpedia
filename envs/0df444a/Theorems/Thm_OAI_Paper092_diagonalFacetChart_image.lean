-- Prove2me | Theorems.Thm_OAI_Paper092_diagonalFacetChart_image
-- name    : OAI.Paper092.diagonalFacetChart_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:19:20.720218+00:00
-- url     : https://prove2.me/theorems/8f09cacf-1c0e-4616-abba-0fca1c74f32c
-- title:
--   The chart inserting $1-\sum_j x_j$ maps $\Delta_n$ onto the slanted facet of $\Delta_{n+1}$
-- statement:
--   Let $\Delta_m=\operatorname{conv}\{0,e_0,\dots,e_{m-1}\}=\{x\in\mathbb{R}^m: x_j\ge0\ \forall j,\ \sum_j x_j\le1\}$ be the standard simplex in $\mathbb{R}^m$ (coordinates indexed from $0$), and let $F_\ast^{(m)}=\{y\in\Delta_m: \sum_k y_k=1\}$ be its slanted facet, the facet opposite the vertex $0$.
--
--   Fix $n\in\mathbb{N}$ and $i\in\{0,\dots,n\}$, and define $\phi_i:\mathbb{R}^n\to\mathbb{R}^{n+1}$ by inserting $1-\sum_j x_j$ in position $i$:
--   $$
--   \phi_i(x)_i=1-\sum_{j=0}^{n-1}x_j,\qquad \phi_i(x)_{\sigma_i(j)}=x_j\quad(0\le j<n),
--   $$
--   where $\sigma_i$ is the increasing bijection from $\{0,\dots,n-1\}$ onto $\{0,\dots,n\}\setminus\{i\}$.
--
--   **Theorem.**
--   $$
--   \phi_i(\Delta_n)=F_\ast^{(n+1)}=\Big\{y\in\Delta_{n+1}: \sum_{k=0}^{n}y_k=1\Big\}.
--   $$
--
--   The chart is affine, $\phi_i(x)=e_i+L_{i,-1}x$ where $L_{i,-1}$ inserts $-\sum_j x_j$ in position $i$, so the theorem presents the slanted facet as a translate of a linear image of $\Delta_n$. This is the parametrization used to compute the area of the slanted facet and of the corresponding facets of products of simplices.
--
--   **Formalization Note** $\phi_i$ is `diagonalFacetChart n i` and $F_\ast^{(n+1)}$ is `simplexFacet (n+1) none`, defined by the vanishing of the simplex coordinate `simplexCoordinates y none`, which equals $1-\sum_k y_k$. The affine relation $\phi_i(x)=e_i+L_{i,-1}x$ is a separate lemma and not part of this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/FacetAreas.lean#L113-L139

import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas

open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

theorem OAI.Paper092.diagonalFacetChart_image (n : ℕ) (i : Fin (n + 1)) :
    diagonalFacetChart n i '' standardSimplex n = simplexFacet (n + 1) none := by sorry
