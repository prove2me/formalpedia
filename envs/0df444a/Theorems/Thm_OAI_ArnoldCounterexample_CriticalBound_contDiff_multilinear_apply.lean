-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_contDiff_multilinear_apply
-- name    : OAI.ArnoldCounterexample.CriticalBound.contDiff_multilinear_apply
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:19:07.820978+00:00
-- url     : https://prove2.me/theorems/1e177d5e-bec5-4a4d-9d0b-e83027f17955
-- title:
--   Evaluating a smooth family of multilinear maps at smooth arguments is smooth
-- statement:
--   Let $E,F,G$ be real normed spaces, $k$ a smoothness degree, and $n\in\mathbb{N}$. Let $f:E\to L^n(F;G)$ be a $C^k$ map into the continuous $n$-multilinear maps, and let $v_1,\dots,v_n:E\to F$ be $C^k$. Then
--   $$
--   x\longmapsto f(x)\bigl(v_1(x),\dots,v_n(x)\bigr)
--   $$
--   is $C^k$.
--
--   This is the regularity statement needed to differentiate expressions such as a differential form evaluated on vector fields, as in Cartan's formula for the exterior derivative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Differentiation.lean#L14-L32

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
universe uE uF uG
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

theorem OAI.ArnoldCounterexample.CriticalBound.contDiff_multilinear_apply {E : Type uE} {F : Type uF} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ∞ω} {n : ℕ} {f : E → F [×n]→L[ℝ] G}
    (hf : ContDiff ℝ k f) {v : Fin n → E → F} (hv : ∀ i, ContDiff ℝ k (v i)) :
    ContDiff ℝ k (fun x ↦ f x (v · x)) := by sorry
