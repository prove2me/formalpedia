-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singular_geometric_cover
-- name    : OAI.RuledApproximation.singular_geometric_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:16:41.463444+00:00
-- url     : https://prove2.me/theorems/5163e43e-1471-4bd5-8209-e599ad41d95d
-- title:
--   Two singular ruled families and two edge prisms cover the regular tetrahedron
-- statement:
--   Let $1<p<2$ and let $\gamma\in\mathbb{R}$ satisfy $1+\gamma(p-2)>0$, i.e. $\gamma<1/(2-p)$. Let $V_p$ be the singular field
--
--   $$
--   V_p(z)=\Big(\tfrac14\,(2z_1)^{p-1}\Big(p+(2-p)\,\frac{z_0^2}{z_1^2}\Big),\ \ (2z_1)^{p-2}\,z_0\Big),\qquad z=(z_0,z_1),
--   $$
--
--   let $\Delta_p(b)=b^2\big(\tfrac p4+(2-p)b^2\big)$, and for $c>0$ let $\Omega_c=\Omega_{p,\gamma,c}$ be the base domain of all $b=(b_0,b_1)\in\mathbb{R}^2$ with $c^\gamma\le b_1\le2$, $|b_0|\le b_1$ and $b_1\le\tfrac12+c^2\Delta_p(b_0)+c^{5/2}$. In $\mathbb{R}^3$ with coordinates $(z_0,z_1,z_2)$ consider:
--
--   - the regular tetrahedron with edge length $2$ and vertices $(\pm1,0,0)$, $(0,\pm1,\sqrt2)$: $\mathcal T=\{z:\ \exists\,t\in[0,1],\ |z_0|\le1-t,\ |z_1|\le t,\ z_2=\sqrt2\,t\}$;
--   - the lower singular ruled piece $L_c=\big\{\big(s,\ b_0+s\,c\,V_p(b)_0,\ \sqrt2\,(b_1+s\,c\,V_p(b)_1)\big):\ b\in\Omega_c,\ |s|\le1\big\}$;
--   - the upper singular ruled piece $U_c=\big\{\big(b_0-c\,y\,V_p(b)_0,\ y,\ \sqrt2\,(1-b_1+c\,y\,V_p(b)_1)\big):\ b\in\Omega_c,\ |y|\le1\big\}$;
--   - for $\delta\in\mathbb{R}$, the edge prisms $P^{\mathrm{low}}_\delta=\{z:\ \exists\,t\in[0,2\delta],\ |z_1|\le t,\ z_2=\sqrt2\,t\}$ and $P^{\mathrm{up}}_\delta=\{z:\ \exists\,s\in[0,2\delta],\ |z_0|\le s,\ z_2=\sqrt2\,(1-s)\}$, which are unbounded in the $z_0$-direction and the $z_1$-direction respectively.
--
--   **Theorem.** There is $c_0>0$ such that for every $c\in(0,c_0)$
--
--   $$
--   \mathcal T\subseteq L_c\cup U_c\cup P^{\mathrm{low}}_{c^\gamma}\cup P^{\mathrm{up}}_{c^\gamma}.
--   $$
--
--   The piece $L_c$ is the union of the segments $s\mapsto(0,b_0,\sqrt2\,b_1)+s\,\big(1,\,c\,V_p(b)_0,\,\sqrt2\,c\,V_p(b)_1\big)$, $|s|\le1$, which for $c=0$ would be parallel to the bottom edge of $\mathcal T$; $U_c$ is the image of $L_c$ under the symmetry $(z_0,z_1,z_2)\mapsto(z_1,-z_0,\sqrt2-z_2)$ of $\mathcal T$, which exchanges the bottom and the top edge. The prisms have triangular cross-sections and cover thin neighbourhoods of these two edges. This inclusion is the covering half of the singular statement of the main theorem: covering each of the four pieces by cylinders of the prescribed shapes gives a cylinder cover of the tetrahedron, whose total area is estimated separately.
--
--   **Formalization Note** The sets are `tetrahedron`, `singularLower p gamma c`, `singularUpper p gamma c`, `lowerTip (c^gamma)` and `upperTip (c^gamma)`; $L_c$ is the physical ruled set `physicalRuled (Real.sqrt 2) (singularDomain p gamma c) (fun b => c • singularField p b) 1`. "For every sufficiently small $c>0$" is the filter statement `∀ᶠ c in 𝓝[>] 0`. No sign condition on $\gamma$ is imposed; in the main theorem $1<\gamma<1/(2-p)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularGeometry.lean#L12-L74

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.singular_geometric_cover {p gamma : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hpg : 0 < 1+gamma*(p-2)) :
    ∀ᶠ c : ℝ in 𝓝[>] 0,
      tetrahedron ⊆ singularLower p gamma c ∪ singularUpper p gamma c ∪
        lowerTip (c^gamma) ∪ upperTip (c^gamma) := by sorry
