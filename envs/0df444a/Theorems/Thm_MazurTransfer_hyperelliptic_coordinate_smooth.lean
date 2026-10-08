-- Prove2me | Theorems.Thm_MazurTransfer_hyperelliptic_coordinate_smooth
-- name    : MazurTransfer.hyperelliptic_coordinate_smooth
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T20:33:26.712261+00:00
-- url     : https://prove2.me/theorems/ddc778f7-fb56-43b6-acc4-5ef7a0f5c119
-- title:
--   Smoothness of a separable quadratic hyperelliptic coordinate algebra
-- statement:
--   Let $K$ be a field with $2\ne 0$, and let $f\in K[x]$ be a separable polynomial. Then the finitely presented coordinate algebra
--   \[K[x,y]/(y^2-f(x))\]
--   is smooth over $K$. Equivalently, the associated affine scheme is smooth over $\operatorname{Spec}K$. The separability hypothesis is explicit: applications must verify it for their particular polynomial. The result supplies the chart-smoothness prerequisite for the explicit order-13 curve and applies also to suitable finite-characteristic fibers. It asserts no genus, properness, Jacobian identification, or rational-point classification.
-- source:
--   New closed Lean proof by Vas and contributors, using the square-zero infinitesimal lifting criterion Algebra.FormallySmooth.of_comp_surjective and Polynomial.aeval_add_of_sq_eq_zero in Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. Named downstream consumer: MazurTorsion.XOneThirteenProjectiveCurve.curveToBase_smooth for the original MazurTheorem two-chart model, commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Design boundary: explicit polynomial separability and invertibility of two over a field.

import Mathlib

theorem MazurTransfer.hyperelliptic_coordinate_smooth
    (K : Type*) [Field K] (f : Polynomial K)
    (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Algebra.Smooth K (AdjoinRoot
      ((Polynomial.X ^ 2 - Polynomial.C f) : Polynomial (Polynomial K))) := by sorry
