-- Prove2me | Theorems.Thm_OAI_Paper092_facetEmbedding_zero_image
-- name    : OAI.Paper092.facetEmbedding_zero_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:18:51.793133+00:00
-- url     : https://prove2.me/theorems/fc0af741-c855-4722-92e0-069eb50a7cd1
-- title:
--   Inserting a zero coordinate maps $\Delta_n$ onto the facet $\{y_i=0\}$ of $\Delta_{n+1}$
-- statement:
--   For $m\in\mathbb{N}$ let $\Delta_m=\operatorname{conv}\{0,e_0,\dots,e_{m-1}\}\subset\mathbb{R}^m$ be the standard (corner) simplex; equivalently $\Delta_m=\{x\in\mathbb{R}^m: x_j\ge0\text{ for all }j,\ \sum_j x_j\le1\}$. Coordinates are indexed from $0$. For a position $i\in\{0,\dots,m-1\}$ the coordinate facet of $\Delta_m$ is $F_i^{(m)}=\{y\in\Delta_m: y_i=0\}$.
--
--   Fix $n\in\mathbb{N}$ and $i\in\{0,\dots,n\}$, and let $L_{i,0}:\mathbb{R}^n\to\mathbb{R}^{n+1}$ be the linear map that inserts a zero in position $i$: $(L_{i,0}x)_i=0$ and $(L_{i,0}x)_{\sigma_i(j)}=x_j$, where $\sigma_i$ is the increasing bijection from $\{0,\dots,n-1\}$ onto $\{0,\dots,n\}\setminus\{i\}$.
--
--   **Theorem.**
--   $$
--   L_{i,0}(\Delta_n)=F_i^{(n+1)}=\{y\in\Delta_{n+1}: y_i=0\}.
--   $$
--
--   Since $L_{i,0}$ preserves norms, this exhibits every coordinate facet of $\Delta_{n+1}$ as an isometric copy of $\Delta_n$. It is the parametrization used to compute the $n$-dimensional areas of the coordinate facets of simplices and of products of simplices.
--
--   **Formalization Note** $L_{i,0}$ is `facetEmbedding n i 0` (the case $c=0$ of the map inserting $c\sum_j x_j$), $\Delta_m$ is `standardSimplex m`, and $F_i^{(n+1)}$ is `simplexFacet (n+1) (some i)`, defined through the simplex coordinate `simplexCoordinates y (some i)`, which is the $i$-th coordinate of $y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/FacetAreas.lean#L76-L93

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

theorem OAI.Paper092.facetEmbedding_zero_image (n : ℕ) (i : Fin (n + 1)) :
    facetEmbedding n i 0 '' standardSimplex n = simplexFacet (n + 1) (some i) := by sorry
