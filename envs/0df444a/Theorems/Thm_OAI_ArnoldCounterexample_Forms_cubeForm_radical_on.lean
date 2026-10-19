-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Forms_cubeForm_radical_on
-- name    : OAI.ArnoldCounterexample.Forms.cubeForm_radical_on
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:27:42.240293+00:00
-- url     : https://prove2.me/theorems/586ab178-4aec-4506-853c-46d2ed0799a5
-- title:
--   The cube $B^{\wedge3}$ of a skew form vanishes if one input is $B$-orthogonal to all others
-- statement:
--   Let $E$ be a real normed space and $B$ a continuous skew-symmetric bilinear form on $E$, $B(u,v)=-B(v,u)$. Let $B^{\wedge3}$ be the alternating $6$-form $B\wedge(B\wedge(B\wedge1))$. If $u,v_1,\dots,v_5\in E$ satisfy $B(u,v_i)=0$ for $i=1,\dots,5$, then
--   $$
--   B^{\wedge3}(u,v_1,\dots,v_5)=0 .
--   $$
--
--   A top power of a skew form vanishes on a tuple containing a vector of the radical of $B$ restricted to the span of the tuple. This is used to show that the third symplectic power vanishes on degenerate configurations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Exterior.lean#L100-L122

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
universe uE uF
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open scoped BigOperators ContDiff
open ContinuousAlternatingMap
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.ArnoldCounterexample.Forms.cubeForm_radical_on (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hskew : ∀ u v, B u v = - B v u) (u : E) (v : Fin 5 → E)
    (horth : ∀ i, B u (v i) = 0) : cubeForm B (Matrix.vecCons u v) = 0 := by sorry
