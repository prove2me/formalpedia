-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Forms_contDiff_pullback_form
-- name    : OAI.ArnoldCounterexample.Forms.contDiff_pullback_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:29:13.667781+00:00
-- url     : https://prove2.me/theorems/9a763e52-34c6-4b9d-8e5c-7574037faeb9
-- title:
--   Pullbacks of a smooth family of forms by a smooth family of linear maps are smooth
-- statement:
--   Let $D,E,F$ be real normed spaces with $E$ finite-dimensional, $n\in\mathbb{N}$, and $k$ a smoothness degree. Let $x\mapsto\theta_x$ be a $C^k$ family of continuous alternating $n$-forms on $F$, and $x\mapsto L_x$ a $C^k$ family of continuous linear maps $E\to F$, both parametrized by $x\in D$. Then the family of pullbacks
--   $$
--   x\longmapsto L_x^*\theta_x,\qquad (L_x^*\theta_x)(v_1,\dots,v_n)=\theta_x(L_xv_1,\dots,L_xv_n),
--   $$
--   is a $C^k$ family of alternating $n$-forms on $E$.
--
--   This regularity statement makes the pullback of a constant form by the derivative of a smooth map a smooth differential form, so that exterior derivatives and homotopy formulas apply to it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Homotopy.lean#L114-L138

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
import Definitions.Def_OAI_Geometry_Arnold_Homotopy

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
universe uE uD uF
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open scoped BigOperators ContDiff
open ContinuousAlternatingMap
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.ArnoldCounterexample.Forms.contDiff_pullback_form {D : Type uD} {F : Type uF}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] {n : ℕ} {k : ℕ∞ω}
    {θ : D → F [⋀^Fin n]→L[ℝ] ℝ} {L : D → E →L[ℝ] F}
    (hθ : ContDiff ℝ k θ) (hL : ContDiff ℝ k L) :
    ContDiff ℝ k (fun x ↦ (θ x).compContinuousLinearMap (L x)) := by sorry
