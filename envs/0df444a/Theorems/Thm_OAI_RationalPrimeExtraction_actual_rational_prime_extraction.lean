-- Prove2me | Theorems.Thm_OAI_RationalPrimeExtraction_actual_rational_prime_extraction
-- name    : OAI.RationalPrimeExtraction.actual_rational_prime_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:27:24.300206+00:00
-- url     : https://prove2.me/theorems/2154f26c-7d07-4d05-9b07-24a7d42d89c1
-- title:
--   Rational Prime Extraction: actual rational prime extraction
-- statement:
--   The Rational Prime Extraction construction uses the actual rational prime extraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L332-L380
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L332-L380

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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.RationalPrimeExtraction
open ActualEisensteinCubic ShortDraftLatticeCount

theorem OAI.RationalPrimeExtraction.actual_rational_prime_extraction
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      (∀ n ∈ columns, qNat n ≤ D) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖∑ n ∈ columns, weight n‖ ≤
        1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by sorry
