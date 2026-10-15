-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singularField_homogeneous_bounds
-- name    : OAI.RuledApproximation.singularField_homogeneous_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:09:21.880385+00:00
-- url     : https://prove2.me/theorems/88a09fd3-8613-484d-9937-29d486d92454
-- title:
--   Homogeneous bounds for the singular model field and its derivative on the cone $|z_1|\le 2z_2$
-- statement:
--   For a real parameter $p$, the *singular model field* $\varphi_p:\mathbb{R}^2\to\mathbb{R}^2$ is given, at points $z=(z_1,z_2)$ with $z_2>0$, by
--   $$\varphi_p(z)=\Bigl(\tfrac14\,(2z_2)^{p-1}\Bigl(p+(2-p)\frac{z_1^2}{z_2^2}\Bigr),\ \ (2z_2)^{p-2}\,z_1\Bigr),$$
--   where $(2z_2)^s$ is the real power of the positive number $2z_2$. Write $D\varphi_p(z)$ for its derivative at $z$.
--
--   **Theorem.** For every real $p$ there is a constant $C\ge1$ such that for all $z\in\mathbb{R}^2$ with $z_2>0$ and $|z_1|\le 2z_2$,
--   $$\|\varphi_p(z)\|\le C\,z_2^{\,p-1}\qquad\text{and}\qquad \|D\varphi_p(z)\|\le C\,z_2^{\,p-2},$$
--   where $\|\varphi_p(z)\|$ is the Euclidean norm and $\|D\varphi_p(z)\|$ the corresponding operator norm.
--
--   These bounds give uniform control of the field and its derivative on the cone $|z_1|\le 2z_2$ all the way to the singular vertex. For instance, for $p<2$, $c>0$ and a real exponent $\gamma$, on the part of the cone where $z_2\ge c^{\gamma}$ they yield $|c|\,\|D\varphi_p(z)\|\le C\,c^{\,1+\gamma(p-2)}$, which is small when $1+\gamma(p-2)>0$; this is the kind of smallness required to apply the scaled hyperbolicity lemma to $c\,\varphi_p$.
--
--   **Formalization Note** The field is `singularField p`; the Lean formula writes the constants as `(1/2)/2` and `b 1/(1/2)`, i.e. $\tfrac14$ and $2z_2$, and uses the real power `Real.rpow`. The coordinates $z_1,z_2$ are `z 0`, `z 1`. Outside the half-plane $z_2>0$ the Lean formula uses the conventions for powers of nonpositive numbers and division by zero, but no statement here depends on those values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularBounds.lean#L25-L67

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

theorem OAI.RuledApproximation.singularField_homogeneous_bounds (p : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : Plane, 0 < z 1 → |z 0| ≤ 2*z 1 →
      ‖singularField p z‖ ≤ C*(z 1)^(p-1) ∧
      ‖fderiv ℝ (singularField p) z‖ ≤ C*(z 1)^(p-2) := by sorry
