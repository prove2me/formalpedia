-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singular_overlap_small
-- name    : OAI.RuledApproximation.singular_overlap_small
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:16:18.288491+00:00
-- url     : https://prove2.me/theorems/d82659c7-9eb3-4a7f-9337-8de393f99bba
-- title:
--   Overlap lemma: one of two matched base points lies under the ceiling of the singular domain
-- statement:
--   Let $V_p$ be the singular field
--
--   $$
--   V_p(z)=\Big(\tfrac14\,(2z_1)^{p-1}\Big(p+(2-p)\,\frac{z_0^2}{z_1^2}\Big),\ \ (2z_1)^{p-2}\,z_0\Big),\qquad z=(z_0,z_1),
--   $$
--
--   with components $V_p(z)_0,V_p(z)_1$, and let $\Delta_p(b)=b^2\big(\tfrac p4+(2-p)b^2\big)$.
--
--   **Theorem.** Let $0\le p\le2$. There is a constant $K\ge1$ such that the following holds for all real numbers $c,x,y$ and all points $z^{-}=(z^{-}_0,z^{-}_1)$ and $z^{+}=(z^{+}_0,z^{+}_1)$ of $\mathbb{R}^2$. Assume $0\le c\le1$, $cK\le\tfrac12$, $16K^2c^3\le2c^{5/2}$, $|x|\le1$, $|y|\le1$, $|z^{-}_0|\le z^{-}_1\le2$, $|z^{+}_0|\le z^{+}_1\le2$, and
--
--   $$
--   z^{-}_0=y-c\,x\,V_p(z^{-})_0,\qquad z^{+}_0=x+c\,y\,V_p(z^{+})_0,\qquad z^{-}_1+z^{+}_1=1+c\big(y\,V_p(z^{+})_1-x\,V_p(z^{-})_1\big).
--   $$
--
--   Then
--
--   $$
--   z^{-}_1\le\tfrac12+c^2\Delta_p(z^{-}_0)+c^{5/2}\qquad\text{or}\qquad z^{+}_1\le\tfrac12+c^2\Delta_p(z^{+}_0)+c^{5/2}.
--   $$
--
--   Geometrically, in the singular covering of the regular tetrahedron $\{(x,y,\sqrt2\,t):\ |x|\le1-t,\ |y|\le t\}$, a point $(x,y,\sqrt2\,t)$ lies on the segment of the lower family with base point $z^{-}$ when $(y,t)=z^{-}+c\,x\,V_p(z^{-})$, and on the segment of the upper family with base point $z^{+}$ when $(x,1-t)=z^{+}-c\,y\,V_p(z^{+})$; eliminating $t$ gives exactly the three displayed equations. The lemma says that at least one of the two base points satisfies the ceiling constraint of the base domain, so that the two truncated families together still cover the middle of the tetrahedron.
--
--   **Formalization Note** The points are `zm` and `zp` in `Plane`, the field is `singularField p` and $\Delta_p$ is `ceilingPolynomial p`. The formula for $V_p$ is used literally at every point (with Lean's conventions for division by $0$ and real powers), so no positivity of $z^{\pm}_1$ is assumed; $c^{5/2}$ is the real power `c^(5/2:ℝ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularOverlap.lean#L202-L229

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

theorem OAI.RuledApproximation.singular_overlap_small {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c x y : ℝ) (zm zp : Plane),
      0 ≤ c → c ≤ 1 → c*K ≤ 1/2 → 16*K^2*c^3 ≤ 2*c^(5/2:ℝ) →
      |x| ≤ 1 → |y| ≤ 1 → zm 1 ≤ 2 → zp 1 ≤ 2 →
      |zm 0| ≤ zm 1 → |zp 0| ≤ zp 1 →
      zm 0=y-c*x*singularField p zm 0 → zp 0=x+c*y*singularField p zp 0 →
      zm 1+zp 1=1+c*(y*singularField p zp 1-x*singularField p zm 1) →
      zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ) ∨
      zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ) := by sorry
