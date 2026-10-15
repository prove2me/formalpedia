-- Prove2me | Theorems.Thm_OAI_Paper092_productWitness_brightness
-- name    : OAI.Paper092.productWitness_brightness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:25:11.751306+00:00
-- url     : https://prove2.me/theorems/e0bed811-d405-4ca6-b1af-40f5d9d2386b
-- title:
--   Brightness function of the product of simplices $\Delta_{10}\times\Delta_{10}$ in $\mathbb{R}^{20}$
-- statement:
--   Write $x\in\mathbb{R}^{20}$ as $x=(x',x'')$ with $x'=(x_0,\dots,x_9)$ and $x''=(x_{10},\dots,x_{19})$, and let $P=\{x\in\mathbb{R}^{20}: x'\in\Delta_{10},\ x''\in\Delta_{10}\}$, where $\Delta_{10}=\{z\in\mathbb{R}^{10}: z_j\ge0,\ \sum_j z_j\le1\}$ is the standard simplex (the convex hull of $0$ and the unit vectors). For $u\in\mathbb{R}^{20}$ the brightness of $P$ in direction $u$ is $b_P(u)=\|u\|\cdot\mathrm{vol}_{u^\perp}(\pi_uP)$, where $\pi_u$ is the orthogonal projection onto $u^\perp=\{y:\langle u,y\rangle=0\}$ and $\mathrm{vol}_{u^\perp}$ is Lebesgue measure on that subspace.
--
--   **Theorem.** For every $u=(u',u'')\in\mathbb{R}^{20}$,
--   $$
--   b_P(u)=\frac{\sum_{j=0}^{9}|u'_j|+\Big|\sum_{j=0}^{9}u'_j\Big|+\sum_{j=0}^{9}|u''_j|+\Big|\sum_{j=0}^{9}u''_j\Big|}{2\cdot9!\cdot10!}.
--   $$
--
--   The projection body of $P$ is $\Pi P=\{y:\langle u,y\rangle\le b_P(u)\text{ for all }u\}$, and the right-hand side is the support function of the zonotope $\frac{1}{10!}Z_{10}\times\frac{1}{10!}Z_{10}$, where $Z_{10}\subset\mathbb{R}^{10}$ is the Minkowski sum of the centred segments $\big[-\frac{e_j}{2\cdot9!},\frac{e_j}{2\cdot9!}\big]$ ($0\le j\le9$) and $\big[-\frac{\mathbf 1}{2\cdot9!},\frac{\mathbf 1}{2\cdot9!}\big]$. This formula is therefore what identifies $\Pi P$ with that product zonotope in the computation of the normalized projection volume $\mathrm{vol}(\Pi P)/\mathrm{vol}(P)^{19}$.
--
--   **Formalization Note** $P$ is `productWitness`, $u'$ and $u''$ are `firstBlock u` and `secondBlock u`, and $b_P(u)$ is `brightness productWitness u`, which uses the real value (`ENNReal.toReal`) of the shadow volume. For $u=0$ both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProductBrightness.lean#L65-L90

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

theorem OAI.Paper092.productWitness_brightness (u : Euclidean 20) :
    brightness productWitness u =
      ((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i| +
        (∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|) /
          (2 * (Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by sorry
