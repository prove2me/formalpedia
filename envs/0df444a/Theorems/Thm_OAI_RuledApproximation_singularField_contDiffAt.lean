-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singularField_contDiffAt
-- name    : OAI.RuledApproximation.singularField_contDiffAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:03:56.670745+00:00
-- url     : https://prove2.me/theorems/abf82002-fa86-4975-ac53-d2b429dac512
-- title:
--   The singular model field is smooth on the open upper half-plane
-- statement:
--   For a real parameter $p$, the *singular model field* $\varphi_p:\mathbb{R}^2\to\mathbb{R}^2$ is given, at points $z=(z_1,z_2)$ with $z_2>0$, by
--   $$\varphi_p(z)=\Bigl(\tfrac14\,(2z_2)^{p-1}\Bigl(p+(2-p)\frac{z_1^2}{z_2^2}\Bigr),\ \ (2z_2)^{p-2}\,z_1\Bigr),$$
--   where $(2z_2)^s$ is the real power of the positive number $2z_2$.
--
--   **Theorem.** For every real $p$ and every point $z\in\mathbb{R}^2$ with $z_2>0$, the map $\varphi_p$ is $C^\infty$ at $z$:
--   $$z_2>0\ \Longrightarrow\ \varphi_p \text{ is infinitely differentiable at } z .$$
--
--   The field $\varphi_p$ is the explicit vector field used for the singular (tetrahedron) case of the main covering theorem. Its smoothness on the open half-plane $\{z_2>0\}$ provides the regularity needed by the local covering machinery and underlies the formulas for its derivative and the homogeneity of that derivative.
--
--   **Formalization Note** The field is `singularField p`; the Lean formula writes the constants as `(1/2)/2` and `b 1/(1/2)`, i.e. $\tfrac14$ and $2z_2$, and uses the real power `Real.rpow`. The coordinates $z_1,z_2$ are `z 0`, `z 1`. Outside the half-plane $z_2>0$ the Lean formula uses the conventions for powers of nonpositive numbers and division by zero, but no statement here depends on those values. The conclusion is `ContDiffAt ℝ ∞ (singularField p) z`, where `∞` is the smooth (not analytic) level.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularField.lean#L25-L39

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

theorem OAI.RuledApproximation.singularField_contDiffAt (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (singularField p) z := by sorry
