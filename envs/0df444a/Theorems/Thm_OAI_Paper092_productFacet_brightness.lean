-- Prove2me | Theorems.Thm_OAI_Paper092_productFacet_brightness
-- name    : OAI.Paper092.productFacet_brightness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:24:11.565669+00:00
-- url     : https://prove2.me/theorems/811979b6-f841-4915-961f-2aeedbf5b363
-- title:
--   Brightness of each of the 22 facets of $\Delta_{10}\times\Delta_{10}$ is $|\nu_a(u)|/(9!\,10!)$
-- statement:
--   Write a vector of $\mathbb{R}^{20}$ as $x=(x',x'')$ with first block $x'=(x_0,\dots,x_9)$ and second block $x''=(x_{10},\dots,x_{19})$, and let $P=\{x: x'\in\Delta_{10},\ x''\in\Delta_{10}\}$ be the product of two copies of the standard simplex $\Delta_{10}=\{z\in\mathbb{R}^{10}: z_j\ge0,\ \sum_j z_j\le1\}$. The facets of $P$ carry the 22 labels $a\in\{(1,j),(1,\ast),(2,j),(2,\ast): 0\le j\le9\}$, with affine facet coordinates
--   $$
--   \lambda_{(1,j)}(x)=x'_j,\quad \lambda_{(1,\ast)}(x)=1-\sum_k x'_k,\quad \lambda_{(2,j)}(x)=x''_j,\quad \lambda_{(2,\ast)}(x)=1-\sum_k x''_k ,
--   $$
--   so that $P=\{x:\lambda_a(x)\ge0\text{ for all }a\}$, and the facet with label $a$ is $F_a=\{x\in P:\lambda_a(x)=0\}$. For $u\in\mathbb{R}^{20}$ let $\nu_a(u)$ be the rate of change of $\lambda_a$ in direction $u$: $\nu_{(1,j)}(u)=u'_j$, $\nu_{(1,\ast)}(u)=-\sum_k u'_k$, and likewise $\nu_{(2,j)}(u)=u''_j$, $\nu_{(2,\ast)}(u)=-\sum_k u''_k$. Finally, $b_K(u)=\|u\|\cdot\mathrm{vol}_{u^\perp}(\pi_uK)$ is the brightness of $K$ in direction $u$, where $\pi_u$ is the orthogonal projection onto $u^\perp=\{y:\langle u,y\rangle=0\}$ and $\mathrm{vol}_{u^\perp}$ is Lebesgue measure on that subspace.
--
--   **Theorem.** For every facet label $a$ and every $u\in\mathbb{R}^{20}$,
--   $$
--   b_{F_a}(u)=\frac{|\nu_a(u)|}{9!\cdot10!}.
--   $$
--
--   Each facet lies in a hyperplane, so its brightness is its 19-dimensional area times $|\langle u,n_a\rangle|$ for a unit normal $n_a$; the theorem packages the four kinds of facets (coordinate or slanted, first or second block) into a single formula. Summing it over the facets visible from direction $u$ yields the brightness function of $P$.
--
--   **Formalization Note** Facet labels form the type `ProductFacetIndex`, that is `Option (Fin 10) ⊕ Option (Fin 10)`, where `inl`/`inr` select the block and `none` is the slanted facet. $\lambda_a(x)$ is `productCoordinates x a`, $\nu_a(u)$ is `productVelocity u a`, $F_a$ is `productFacet a`, $P$ is `productWitness`, and $b$ is the real-valued `brightness` (shadow volume taken through `ENNReal.toReal`). For $u=0$ both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProductBrightness.lean#L15-L63

import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian

open OAI OAI.Paper092
open Set MeasureTheory
open scoped RealInnerProductSpace

theorem OAI.Paper092.productFacet_brightness (a : ProductFacetIndex) (u : Euclidean 20) :
    brightness (productFacet a) u =
      |productVelocity u a| / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by sorry
