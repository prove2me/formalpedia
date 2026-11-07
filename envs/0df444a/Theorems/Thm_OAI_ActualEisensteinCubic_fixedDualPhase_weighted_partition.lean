-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_fixedDualPhase_weighted_partition
-- name    : OAI.ActualEisensteinCubic.fixedDualPhase_weighted_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:27:39.551194+00:00
-- url     : https://prove2.me/theorems/c1e23316-2961-4170-82bd-fe4d05fadbc6
-- title:
--   Actual Eisenstein Cubic: fixed Dual Phase weighted partition
-- statement:
--   The Actual Eisenstein Cubic construction uses the fixed Dual Phase weighted partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L506-L540
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L506-L540

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex

theorem OAI.ActualEisensteinCubic.fixedDualPhase_weighted_partition (c : O) (W : O → ℂ)
    (hsum : Summable (fun y : O => fixedDualPhase c y * W y)) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑' y : O, fixedDualPhase c y * W y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
          ∑' w : O,
            W (GaussianShiftedPartition.representative 2 r + 2*w) := by sorry
