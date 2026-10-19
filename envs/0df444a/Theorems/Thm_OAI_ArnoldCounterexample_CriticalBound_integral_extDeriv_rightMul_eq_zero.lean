-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_integral_extDeriv_rightMul_eq_zero
-- name    : OAI.ArnoldCounterexample.CriticalBound.integral_extDeriv_rightMul_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:19:49.875863+00:00
-- url     : https://prove2.me/theorems/2cf1c473-9d87-4066-8bfa-4765530d2a74
-- title:
--   Haar–Stokes on $O(5)$: integrals of $dW$ on left-invariant fields vanish when bracket terms do
-- statement:
--   Let $O(5)$ be the real orthogonal group inside the $5\times5$ real matrices $M_5(\mathbb{R})$, and let $\mu$ be its right-invariant Haar measure (the inverse of a left Haar measure); $O(5)$ is compact and $\mu$ is finite. Let $n\in\mathbb{N}$, and let $W$ be a smooth map from $M_5(\mathbb{R})$ to the continuous alternating $(n+1)$-forms on $M_5(\mathbb{R})$. Let $X_0,\dots,X_{n+1}$ be skew-symmetric matrices. Assume the vertical (bracket) condition: for all $A\in O(5)$ and all $i<j$,
--   $$
--   W_A\Bigl(A[X_i,X_j],\ AX_0,\dots,\widehat{AX_i},\dots,\widehat{AX_j},\dots,AX_{n+1}\Bigr)=0,
--   $$
--   where hats denote omitted entries and $[X,Y]=XY-YX$. Then
--   $$
--   \int_{O(5)}dW(A)\bigl(AX_0,\dots,AX_{n+1}\bigr)\,d\mu(A)=0,
--   $$
--   where $dW$ is the exterior derivative of $W$.
--
--   The bracket condition is purely pointwise and algebraic. Under it, the integral over $O(5)$ of the exterior derivative of a form, evaluated on left-invariant fields, vanishes. This is a Stokes-type identity used to show that a certain integral is a homotopy invariant.
--
--   **Formalization Note** The vertical hypothesis is stated with Lean's index removals: the bracket is placed first, followed by the remaining $AX_k$ in order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Differentiation.lean#L68-L102

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
open VectorField

theorem OAI.ArnoldCounterexample.CriticalBound.integral_extDeriv_rightMul_eq_zero {n : ℕ}
    (W : RM → MatForm (n + 1)) (hW : ContDiff ℝ ∞ W)
    (X : Fin (n + 2) → RM) (hX : ∀ i, star (X i) = -X i)
    (hvertical : ∀ (A : O5) (i j : Fin (n + 1)),
      W A (Matrix.vecCons ((A : RM) * (X i.castSucc * X j.succ - X j.succ * X i.castSucc))
        (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * X k)))) = 0) :
    ∫ A : O5, extDeriv W (A : RM) (fun i ↦ (A : RM) * X i) ∂haar = 0 := by sorry
