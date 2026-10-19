-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Quadric_tangentCurve_hasDerivAt_zero
-- name    : OAI.ArnoldCounterexample.Quadric.tangentCurve_hasDerivAt_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:17:26.124835+00:00
-- url     : https://prove2.me/theorems/116f1154-2070-4be2-a597-e5ac73b0a148
-- title:
--   Every horizontal vector is the velocity of a curve in the unit isotropic quadric
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$, $|z|^2=\sum_j|z_j|^2$ and $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}=S/U(1)$. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0$ and $\sum_jz_jv_j=0$. For $z\in S$ and horizontal $v$, the tangent curve is
--   $$
--   c(t)=\frac{\gamma(t)}{|\gamma(t)|},\qquad \gamma(t)=z+t\,v-\frac{t^2}{2}\,q(v)\,\bar z,
--   $$
--   which lies in $S$ for all real $t$ and satisfies $c(0)=z$. The theorem states that
--   $$
--   c'(0)=v .
--   $$
--
--   So every horizontal vector is realized as the velocity of an actual differentiable curve in the unit quadric. Horizontal vectors therefore model the tangent space of $Q_3$ without assuming a manifold structure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Tangent.lean#L106-L121

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Quadric
open scoped BigOperators ContDiff

theorem OAI.ArnoldCounterexample.Quadric.tangentCurve_hasDerivAt_zero (z : UnitQuadric) (v : CV) (hv : Horizontal z v) :
    HasDerivAt (fun t ↦ (tangentCurve z v hv t : CV)) v 0 := by sorry
