-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singular_region_estimates
-- name    : OAI.RuledApproximation.singular_region_estimates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:15:28.141369+00:00
-- url     : https://prove2.me/theorems/b3f3d131-7c41-4cf9-8463-a58a0243e65f
-- title:
--   Lipschitz-type estimates for the singular field near the level $z_1=\tfrac12$
-- statement:
--   Let $p\in\mathbb{R}$, let $V_p$ be the singular field
--
--   $$
--   V_p(z)=\Big(\tfrac14\,(2z_1)^{p-1}\Big(p+(2-p)\,\frac{z_0^2}{z_1^2}\Big),\ \ (2z_1)^{p-2}\,z_0\Big),\qquad z=(z_0,z_1),
--   $$
--
--   with components $V_p(z)_0,V_p(z)_1$, and let $\Delta_p(b)=b^2\big(\tfrac p4+(2-p)b^2\big)$ be the ceiling polynomial.
--
--   **Theorem.** There is a constant $K\ge1$ such that for every $z=(z_0,z_1)\in\mathbb{R}^2$ and every $B\in\mathbb{R}$ with $|z_0|\le2$, $\tfrac12\le z_1\le2$ and $|B|\le2$:
--
--   1. $|V_p(z)_0|\le K$;
--   2. $|V_p(z)_1-z_0|\le K\,(z_1-\tfrac12)$;
--   3. $\big|V_p(z)_0-\big(\tfrac p4+(2-p)B^2\big)\big|\le K\,\big(|z_0-B|+(z_1-\tfrac12)\big)$;
--   4. $|\Delta_p(z_0)-\Delta_p(B)|\le K\,|z_0-B|$.
--
--   On the level line $z_1=\tfrac12$ the field takes the explicit values $V_p(b,\tfrac12)=\big(\tfrac p4+(2-p)b^2,\ b\big)$. The estimates say that on the rectangle $[-2,2]\times[\tfrac12,2]$ the field $V_p$ and the polynomial $\Delta_p$ deviate from these level values at most linearly in the height above the level and in the horizontal displacement. They are the analytic input of the overlap argument, which shows that the two truncated ruled families of the singular covering together reach the middle of the regular tetrahedron.
--
--   **Formalization Note** The field is `singularField p`, with components `singularField p z 0` and `singularField p z 1`, and $\Delta_p$ is `ceilingPolynomial p`. No restriction on $p$ is needed, because the rectangle stays away from the line $z_1=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularOverlap.lean#L24-L95

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

theorem OAI.RuledApproximation.singular_region_estimates (p : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (z : Plane) (B : ℝ),
      |z 0| ≤ 2 → (1/2:ℝ) ≤ z 1 → z 1 ≤ 2 → |B| ≤ 2 →
      |singularField p z 0| ≤ K ∧
      |singularField p z 1-z 0| ≤ K*(z 1-1/2) ∧
      |singularField p z 0-(p/4+(2-p)*B^2)| ≤ K*(|z 0-B|+(z 1-1/2)) ∧
      |ceilingPolynomial p (z 0)-ceilingPolynomial p B| ≤ K*|z 0-B| := by sorry
