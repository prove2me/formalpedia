-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singular_inverse_small
-- name    : OAI.RuledApproximation.singular_inverse_small
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:13:24.587765+00:00
-- url     : https://prove2.me/theorems/0f43520d-7954-4138-a66e-882ad799817e
-- title:
--   Inverting $z\mapsto z+k\,V_p(z)$ inside the cone for small $k$
-- statement:
--   For a real parameter $p$ let $V_p:\mathbb{R}^2\to\mathbb{R}^2$ be the singular field
--
--   $$
--   V_p(z)=\Big(\tfrac14\,(2z_1)^{p-1}\Big(p+(2-p)\,\frac{z_0^2}{z_1^2}\Big),\ \ (2z_1)^{p-2}\,z_0\Big),\qquad z=(z_0,z_1),
--   $$
--
--   with components $V_p(z)_0$ and $V_p(z)_1$. On the half-plane $z_1>0$ it is smooth and positively homogeneous of degree $p-1$.
--
--   **Theorem.** Let $p<2$. There is a constant $C\ge1$ with the following property. Let $d,c,B,T,k$ be real numbers with
--
--   $$
--   d>0,\qquad c\ge0,\qquad c\,C\,d^{\,p-2}\le\tfrac18,\qquad 2d\le T\le1,\qquad |B|\le T,\qquad |k|\le c .
--   $$
--
--   Then there is a point $z=(z_0,z_1)\in\mathbb{R}^2$ with $d\le z_1\le2$ and $|z_0|\le z_1$ such that
--
--   $$
--   (B,T)=z+k\,V_p(z).
--   $$
--
--   In the singular covering of the regular tetrahedron, the point $(x,B,\sqrt2\,T)$ lies on the ruling of the lower family issued from the base point $b$ exactly when $(B,T)=b+c\,x\,V_p(b)$. The lemma inverts this relation: when $k$ is small compared with $d^{\,2-p}$, every target $(B,T)$ in the cone $|B|\le T$ at height $T\ge2d$ comes from a base point $z$ that again lies in the cone, above height $d$ and below height $2$. With $d=c^\gamma$ this shows that both ruled families reach every point of the tetrahedron outside the two thin prisms around a pair of opposite edges.
--
--   **Formalization Note** The field is `singularField p` and the point $(B,T)$ is `vec2 B T` in `Plane`. The formula for $V_p$ is taken literally at every point (with Lean's conventions for division by $0$ and for real powers); the point $z$ produced has $z_1\ge d>0$, where it is the smooth formula above. The constant $C$ depends only on $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularInverse.lean#L42-L125

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

theorem OAI.RuledApproximation.singular_inverse_small {p : ℝ} (hp2 : p < 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d c B T k : ℝ), 0 < d → 0 ≤ c →
      c*C*d^(p-2) ≤ 1/8 → 2*d ≤ T → T ≤ 1 → |B| ≤ T → |k| ≤ c →
      ∃ z : Plane, d ≤ z 1 ∧ z 1 ≤ 2 ∧ |z 0| ≤ z 1 ∧
        vec2 B T = z+k • singularField p z := by sorry
