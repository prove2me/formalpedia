-- Prove2me | Theorems.Thm_OAI_GaussianAbelPartition_actual_quadratic_gaussian_partition
-- name    : OAI.GaussianAbelPartition.actual_quadratic_gaussian_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:55.871916+00:00
-- url     : https://prove2.me/theorems/ccbda594-4a39-4c4d-bdfe-ba12bac2cb94
-- title:
--   Gaussian Abel Partition: actual quadratic gaussian partition
-- statement:
--   The Gaussian Abel Partition construction uses the actual quadratic gaussian partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L392-L411
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L392-L411

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span

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
open OAI.GaussianAbelPartition
open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic

theorem OAI.GaussianAbelPartition.actual_quadratic_gaussian_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1 := by sorry
