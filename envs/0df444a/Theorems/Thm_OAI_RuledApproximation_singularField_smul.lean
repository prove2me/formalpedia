-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singularField_smul
-- name    : OAI.RuledApproximation.singularField_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:06:25.787748+00:00
-- url     : https://prove2.me/theorems/6d1bbe2c-a317-4e7e-9940-c71d2d551041
-- title:
--   The singular model field is positively homogeneous of degree $p-1$
-- statement:
--   For a real parameter $p$, the *singular model field* $\varphi_p:\mathbb{R}^2\to\mathbb{R}^2$ is given, at points $z=(z_1,z_2)$ with $z_2>0$, by
--   $$\varphi_p(z)=\Bigl(\tfrac14\,(2z_2)^{p-1}\Bigl(p+(2-p)\frac{z_1^2}{z_2^2}\Bigr),\ \ (2z_2)^{p-2}\,z_1\Bigr),$$
--   where $(2z_2)^s$ is the real power of the positive number $2z_2$.
--
--   **Theorem.** For every real $p$, every $r>0$ and every $z\in\mathbb{R}^2$ with $z_2>0$,
--   $$\varphi_p(rz)=r^{\,p-1}\,\varphi_p(z).$$
--
--   Homogeneity reduces all estimates on $\varphi_p$ near the singular point $z=0$ to estimates on a compact cross-section such as $\{(t,1): |t|\le 2\}$, and is the basis for the corresponding homogeneity of the derivative and for uniform bounds of the form $\|\varphi_p(z)\|\le C\,z_2^{\,p-1}$.
--
--   **Formalization Note** The field is `singularField p`; the Lean formula writes the constants as `(1/2)/2` and `b 1/(1/2)`, i.e. $\tfrac14$ and $2z_2$, and uses the real power `Real.rpow`. The coordinates $z_1,z_2$ are `z 0`, `z 1`. Outside the half-plane $z_2>0$ the Lean formula uses the conventions for powers of nonpositive numbers and division by zero, but no statement here depends on those values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularField.lean#L45-L58

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

theorem OAI.RuledApproximation.singularField_smul (p : ℝ) {r : ℝ} (hr : 0 < r) {z : Plane} (hz : 0 < z 1) :
    singularField p (r • z) = r^(p-1) • singularField p z := by sorry
