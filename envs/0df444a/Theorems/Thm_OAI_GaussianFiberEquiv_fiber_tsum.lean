-- Prove2me | Theorems.Thm_OAI_GaussianFiberEquiv_fiber_tsum
-- name    : OAI.GaussianFiberEquiv.fiber_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:55.005121+00:00
-- url     : https://prove2.me/theorems/c687ced4-ad73-42d6-b70b-9f11f8428a87
-- title:
--   Gaussian Fiber Equiv: fiber tsum
-- statement:
--   The Gaussian Fiber Equiv construction uses the fiber tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L499-L507
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L499-L507

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.GaussianFiberEquiv
open ActualEisensteinCubic

theorem OAI.GaussianFiberEquiv.fiber_tsum (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (W : O → ℂ) :
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1) =
      ∑' w : O, W (r0 + c*w) := by sorry
