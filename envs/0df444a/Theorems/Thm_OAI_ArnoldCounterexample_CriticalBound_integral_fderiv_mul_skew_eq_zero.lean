-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_integral_fderiv_mul_skew_eq_zero
-- name    : OAI.ArnoldCounterexample.CriticalBound.integral_fderiv_mul_skew_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:18:24.37901+00:00
-- url     : https://prove2.me/theorems/7566cd8d-8cf9-4037-af0f-971eeb185764
-- title:
--   Haar integrals over $O(5)$ of left-invariant directional derivatives vanish
-- statement:
--   Let $O(5)$ be the real orthogonal group inside the $5\times5$ real matrices $M_5(\mathbb{R})$, and let $\mu$ be its right-invariant Haar measure (the inverse of a left Haar measure); $O(5)$ is compact and $\mu$ is finite. Let $f:M_5(\mathbb{R})\to\mathbb{R}$ be smooth and let $X\in M_5(\mathbb{R})$ be skew-symmetric. Then
--   $$
--   \int_{O(5)}df(A)\bigl[A\,X\bigr]\,d\mu(A)=0 .
--   $$
--
--   The directional derivative of $f$ along the left-invariant vector field $A\mapsto AX$ integrates to zero. This is Stokes' theorem on the closed manifold $O(5)$ in its simplest form, derived here from the invariance of Haar measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Haar.lean#L129-L150

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
universe uG
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped BigOperators
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator ContDiff
attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instContinuousStarRM

theorem OAI.ArnoldCounterexample.CriticalBound.integral_fderiv_mul_skew_eq_zero (f : RM → ℝ) (hf : ContDiff ℝ ∞ f)
    (X : RM) (hX : star X = -X) :
    ∫ A : O5, fderiv ℝ f (A : RM) ((A : RM) * X) ∂haar = 0 := by sorry
