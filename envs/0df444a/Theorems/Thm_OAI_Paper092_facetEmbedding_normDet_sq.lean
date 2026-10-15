-- Prove2me | Theorems.Thm_OAI_Paper092_facetEmbedding_normDet_sq
-- name    : OAI.Paper092.facetEmbedding_normDet_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:18:27.801892+00:00
-- url     : https://prove2.me/theorems/f9a01208-0b54-4440-8786-fb7089c2fada
-- title:
--   Area factor of inserting the coordinate $c\sum_j x_j$: $J(L_{i,c})^2=1+nc^2$
-- statement:
--   Fix $n\in\mathbb{N}$, a position $i\in\{0,1,\dots,n\}$ and a real number $c$. Coordinates of $\mathbb{R}^m$ are indexed by $\{0,\dots,m-1\}$, and $\sigma_i:\{0,\dots,n-1\}\to\{0,\dots,n\}\setminus\{i\}$ denotes the increasing bijection ($\sigma_i(j)=j$ for $j<i$ and $\sigma_i(j)=j+1$ for $j\ge i$). Let $L_{i,c}:\mathbb{R}^n\to\mathbb{R}^{n+1}$ be the linear map that inserts the new coordinate $c\sum_j x_j$ in position $i$:
--   $$
--   (L_{i,c}x)_i=c\sum_{j=0}^{n-1}x_j,\qquad (L_{i,c}x)_{\sigma_i(j)}=x_j\quad(0\le j<n).
--   $$
--   For a linear map $L$ out of a finite-dimensional inner product space, let $J(L)=\sqrt{\det(L^{*}L)}\ge0$ be its norm determinant, the factor by which $L$ multiplies volume of the dimension of its domain.
--
--   **Theorem.** For all $n\in\mathbb{N}$, $i\in\{0,\dots,n\}$ and $c\in\mathbb{R}$,
--   $$
--   J(L_{i,c})^2=1+n\,c^2 .
--   $$
--
--   In particular $L_{i,0}$, which just inserts a zero coordinate, has $J=1$, while $L_{i,-1}$ has $J=\sqrt{n+1}$. These are the area factors of the maps that parametrize the facets of the standard simplex in $\mathbb{R}^{n+1}$ by the standard simplex in $\mathbb{R}^n$: the coordinate facets $\{y_i=0\}$, and (after a translation by $e_i$) the slanted facet $\{\sum_k y_k=1\}$.
--
--   **Formalization Note** $L_{i,c}$ is `facetEmbedding n i c`, built with `Fin.insertNth` on `Euclidean n` (that is, `EuclideanSpace ℝ (Fin n)`); $J$ is Mathlib's `LinearMap.normDet`, whose square equals $\det(L^{*}L)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/FacetAreas.lean#L44-L60

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

theorem OAI.Paper092.facetEmbedding_normDet_sq (n : ℕ) (i : Fin (n + 1)) (c : ℝ) :
    (facetEmbedding n i c).normDet ^ 2 = 1 + (n : ℝ) * c ^ 2 := by sorry
