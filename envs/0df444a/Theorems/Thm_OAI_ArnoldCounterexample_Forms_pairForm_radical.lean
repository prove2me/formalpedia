-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Forms_pairForm_radical
-- name    : OAI.ArnoldCounterexample.Forms.pairForm_radical
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:27:13.693993+00:00
-- url     : https://prove2.me/theorems/ca875210-cbdf-454e-876d-2b0708bb4cdf
-- title:
--   The alternating product $B\wedge\eta$ vanishes on a common radical vector
-- statement:
--   Let $E$ be a real normed space, $B$ a continuous bilinear form on $E$, and $\eta$ a continuous alternating $(n+1)$-form on $E$. Let $B\wedge\eta$ denote the alternating $(n+3)$-form obtained by alternatizing $B\otimes\eta$. Let $u\in E$ satisfy
--   $$
--   B(u,v)=0,\qquad B(v,u)=0\quad\text{for all } v,\qquad \eta(u,v_1,\dots,v_n)=0\quad\text{for all } v_i .
--   $$
--   Then for all $v_0,\dots,v_{n+1}\in E$,
--   $$
--   (B\wedge\eta)(u,v_0,\dots,v_{n+1})=0 .
--   $$
--
--   If every factor annihilates the direction $u$, so does their alternating product. Applied to restrictions to tangent spaces of spheres, this shows that certain forms are basic, i.e. they vanish on the circle direction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Exterior.lean#L37-L63

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

theorem OAI.ArnoldCounterexample.Forms.pairForm_radical {n : ℕ} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (η : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) (u : E)
    (hleft : ∀ v, B u v = 0) (hright : ∀ v, B v u = 0)
    (hη : ∀ v : Fin n → E, η (Matrix.vecCons u v) = 0)
    (v : Fin (n + 2) → E) :
    pairForm B η (Matrix.vecCons u v) = 0 := by sorry
