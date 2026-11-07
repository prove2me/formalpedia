-- Prove2me | Theorems.Thm_OAI_RationalQuant_from_rational_prime_rows_with_constant
-- name    : OAI.RationalQuant.from_rational_prime_rows_with_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:27:22.570547+00:00
-- url     : https://prove2.me/theorems/21838043-c1c5-42c4-b636-688cc786e9ed
-- title:
--   Rational Quant: from rational prime rows with constant
-- statement:
--   The Rational Quant construction uses the from rational prime rows with constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L99-L153
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L99-L153

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
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
open OAI.RationalQuant

theorem OAI.RationalQuant.from_rational_prime_rows_with_constant
    (D ε J A C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hJ : D ^ ((4 / 45 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((31 / 15 : ℝ) + ε) +
      2 * J * C ^ 2 * D ^ (82 / 45 : ℝ)) :
    A ≤ 2 * C * D ^ ((89 / 90 : ℝ) + ε) := by sorry
