-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Forms_cylinder_homotopy_identity
-- name    : OAI.ArnoldCounterexample.Forms.cylinder_homotopy_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:28:31.707799+00:00
-- url     : https://prove2.me/theorems/8f5c24b4-2127-4d7a-8943-d12995999b44
-- title:
--   Homotopy formula on a cylinder: $d(\iota_{\partial_t}\Theta_t)=\partial_t\Theta_t$ on slices for a closed form
-- statement:
--   Let $E$ be a real normed space and $\Theta$ a differentiable family of continuous alternating $(n+1)$-forms on the cylinder $\mathbb{R}\times E$, i.e. a differential $(n+1)$-form on the cylinder. Let $(t,z)$ be a point with $d\Theta(t,z)=0$. Let $\sigma_t$ be the slice contraction, the $n$-form on $E$ given by
--   $$
--   \sigma_t(z)(w_1,\dots,w_n)=\Theta(t,z)\bigl((1,0),(0,w_1),\dots,(0,w_n)\bigr).
--   $$
--   Then for all $v_0,\dots,v_n\in E$,
--   $$
--   d\sigma_t(z)(v_0,\dots,v_n)=\bigl(\partial_t\Theta\bigr)(t,z)\bigl((0,v_0),\dots,(0,v_n)\bigr).
--   $$
--
--   For a closed form, the time derivative of its restriction to the slices $\{t\}\times E$ is exact, with primitive the contraction with $\partial_t$. This is the infinitesimal homotopy formula behind homotopy invariance of integrals of closed forms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Homotopy.lean#L51-L88

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

theorem OAI.ArnoldCounterexample.Forms.cylinder_homotopy_identity {n : ℕ}
    (Θ : ℝ × E → (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (hΘ : Differentiable ℝ Θ) (t : ℝ) (z : E)
    (hclosed : extDeriv Θ (t, z) = 0) (v : Fin (n + 1) → E) :
    extDeriv (sliceContraction Θ t) z v =
      (fderiv ℝ Θ (t, z) (1, 0)) (fun i ↦ (0, v i)) := by sorry
