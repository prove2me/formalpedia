-- Prove2me | Theorems.Thm_MeasureTheory_integral_covector_trace_compl_ball
-- name    : MeasureTheory.integral_covector_trace_compl_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T21:59:18.446992+00:00
-- url     : https://prove2.me/theorems/3f5888a7-4b32-4bf7-87be-07f1b8e26316
-- title:
--   Divergence theorem outside a ball for compactly supported punctured C¹ covector fields
-- statement:
--   Let $n\ge1$, $x\in\mathbb R^n$, and $r>0$. Let $A$ be a covector field with compact support, of class $C^1$ at every point other than $x$. For an orthonormal basis $(e_i)$ write $\operatorname{tr}DA(y)=\sum_i DA(y)[e_i](e_i)$. Then
--
--   $$\int_{\mathbb R^n\setminus B_r(x)}\operatorname{tr}DA(y)\,dy=-r^{n-1}\int_{S^{n-1}}A(x+r\omega)(\omega)\,dS(\omega).$$
--
--   The measure on the unit sphere is the standard surface measure. This is the exterior divergence theorem with the inner-boundary orientation. No value or regularity of the field at the excluded center is needed.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 17, Theorem 1.46; compact-support exterior specialization used on printed p. 35, Eq. (2.20).

import Theorems.Thm_MeasureTheory_integral_directional_derivative_ball
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Function Metric
open scoped Topology
set_option maxHeartbeats 1200000

theorem MeasureTheory.integral_covector_trace_compl_ball {n : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (x : EuclideanSpace ℝ (Fin n))
    (hA : ∀ y, y ≠ x → ContDiffAt ℝ 1 A y)
    (hAc : HasCompactSupport A)
    (r : ℝ) (hr : 0 < r) :
    (∫ y in (ball x r)ᶜ, ∑ i : Fin n,
      fderiv ℝ A y (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      -(r ^ (n - 1)) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        A (x + r • ω.1) ω.1 ∂volume.toSphere := by sorry
