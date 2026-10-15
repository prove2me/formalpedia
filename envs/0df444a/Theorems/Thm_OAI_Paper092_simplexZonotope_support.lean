-- Prove2me | Theorems.Thm_OAI_Paper092_simplexZonotope_support
-- name    : OAI.Paper092.simplexZonotope_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:28:47.764502+00:00
-- url     : https://prove2.me/theorems/a4289068-7cd1-4225-99d7-6fc367a18a08
-- title:
--   Support function of the simplex zonotope $Z_d$: $\big(\sum_i|u_i|+|\sum_i u_i|\big)/(2\,(d-1)!)$
-- statement:
--   For $d\in\mathbb{N}$ let $e_0,\dots,e_{d-1}$ be the standard basis of $\mathbb{R}^d$, $\mathbf 1=\sum_i e_i$ the all-ones vector, and $\kappa=1/(d-1)!$. Define the zonotope
--   $$
--   Z_d=\sum_{i=0}^{d-1}\Big[-\tfrac{\kappa}{2}e_i,\ \tfrac{\kappa}{2}e_i\Big]+\Big[-\tfrac{\kappa}{2}\mathbf 1,\ \tfrac{\kappa}{2}\mathbf 1\Big],
--   $$
--   the Minkowski sum of $d+1$ segments centred at the origin. For a set $K\subseteq\mathbb{R}^d$ and $u\in\mathbb{R}^d$ let $h_K(u)=\sup_{x\in K}\langle u,x\rangle$ be its support function.
--
--   **Theorem.** For every $d\in\mathbb{N}$ and every $u\in\mathbb{R}^d$,
--   $$
--   h_{Z_d}(u)=\frac{\sum_{i=0}^{d-1}|u_i|+\Big|\sum_{i=0}^{d-1}u_i\Big|}{2\,(d-1)!}.
--   $$
--
--   In the surrounding development, for $d\ge1$ this expression is matched with the brightness function of the standard simplex $\Delta_d$, which identifies $Z_d$ as the projection body of $\Delta_d$. Scaled by $1/10!$ and applied blockwise in $\mathbb{R}^{20}=\mathbb{R}^{10}\times\mathbb{R}^{10}$, it gives the support function of the zonotope that matches the brightness function of $\Delta_{10}\times\Delta_{10}$.
--
--   **Formalization Note** $Z_d$ is `simplexZonotope d`, and $h_K(u)$ is `SupportGeometry.support K (innerSL ℝ u)`, defined as `sSup` of the image of $K$ under $x\mapsto\langle u,x\rangle$; the supremum is attained since $Z_d$ is nonempty and compact. The factorial is taken of the natural number $d-1$ with truncated subtraction, so for $d=0$ it reads $0!=1$ and both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexZonotope.lean#L38-L60

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
import Definitions.Def_OAI_Geometry_ProjectionVolume_SupportGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_Extrusion
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexZonotope

open OAI OAI.Paper092
universe uE uι
open Set MeasureTheory
open scoped Pointwise RealInnerProductSpace

theorem OAI.Paper092.simplexZonotope_support (d : ℕ) (u : Euclidean d) :
    SupportGeometry.support (simplexZonotope d) (innerSL ℝ u) =
      ((∑ i : Fin d, |u i|) + |∑ i : Fin d, u i|) / (2 * ((d - 1).factorial : ℝ)) := by sorry
