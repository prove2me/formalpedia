-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singularField_scaled_hyperbolic
-- name    : OAI.RuledApproximation.singularField_scaled_hyperbolic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:08:53.94699+00:00
-- url     : https://prove2.me/theorems/d791dee9-4098-4dde-ad4f-61a7b02631e6
-- title:
--   Small multiples of the singular model field are hyperbolic on the cone $|z_1|\le z_2$
-- statement:
--   For a real parameter $p$, the *singular model field* $\varphi_p:\mathbb{R}^2\to\mathbb{R}^2$ is given, at points $z=(z_1,z_2)$ with $z_2>0$, by $\varphi_p(z)=\bigl(\tfrac14(2z_2)^{p-1}(p+(2-p)z_1^2/z_2^2),\ (2z_2)^{p-2}z_1\bigr)$, where $(2z_2)^s$ is the real power of the positive number $2z_2$. A map $v:\mathbb{R}^2\to\mathbb{R}^2$ is called *hyperbolic at $z$ with time-length $L$* if there is $\lambda\in\mathbb{R}$ with $0<L\lambda<1$ such that both $\lambda$ and $-\lambda$ are eigenvalues of the derivative $Dv(z)$.
--
--   **Theorem.** Let $1<p<2$ and $c\ne0$, and let $z\in\mathbb{R}^2$ satisfy $z_2>0$ and $|z_1|\le z_2$. If
--   $$|c|\,\bigl\|D\varphi_p(z)\bigr\|<1 ,$$
--   where $\|\cdot\|$ is the operator norm for the Euclidean norm, then the field $c\,\varphi_p$ is hyperbolic at $z$ with time-length $1$: there is $\lambda$ with $0<\lambda<1$ such that $\lambda$ and $-\lambda$ are eigenvalues of $D(c\,\varphi_p)(z)$.
--
--   The lemma converts a smallness condition on $|c|\,\|D\varphi_p(z)\|$ into the hyperbolicity hypothesis of the general covering theorem, now for the rescaled field $c\,\varphi_p$ on the cone $|z_1|\le z_2$. This is the form in which the general theorem is applied to the singular ruled pieces in the tetrahedron case of the main covering theorem.
--
--   **Formalization Note** The field is `singularField p`; the Lean formula writes the constants as `(1/2)/2` and `b 1/(1/2)`, i.e. $\tfrac14$ and $2z_2$, and uses the real power `Real.rpow`. The coordinates $z_1,z_2$ are `z 0`, `z 1`. Outside the half-plane $z_2>0$ the Lean formula uses the conventions for powers of nonpositive numbers and division by zero, but no statement here depends on those values. The conclusion is `HyperbolicAt 1 (fun w => c • singularField p w) z`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularField.lean#L189-L210

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

theorem OAI.RuledApproximation.singularField_scaled_hyperbolic {p c : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hc : c ≠ 0) {z : Plane} (hz : 0 < z 1) (hb : |z 0| ≤ z 1)
    (hd : |c| *‖fderiv ℝ (singularField p) z‖ < 1) :
    HyperbolicAt 1 (fun w => c • singularField p w) z := by sorry
