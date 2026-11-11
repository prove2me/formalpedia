-- Prove2me | Theorems.Thm_OAI_CanonicalRowCompletion_outside_separated_cube_coefficient_bound
-- name    : OAI.CanonicalRowCompletion.outside_separated_cube_coefficient_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:56:16.694328+00:00
-- url     : https://prove2.me/theorems/7318b8a5-ee4d-4411-9cab-66210c4036d1
-- title:
--   Canonical Row Completion: outside separated cube coefficient bound
-- statement:
--   The Canonical Row Completion construction uses the outside separated cube coefficient bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RowCompletion/PolynomialHeight.lean#L83-L111
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RowCompletion/PolynomialHeight.lean#L83-L111

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_PolynomialHeight
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
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalCubeSeparation

theorem OAI.CanonicalRowCompletion.outside_separated_cube_coefficient_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (Ψ : ActualEisensteinCubic.O →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m f : ActualEisensteinCubic.O) (H₀ B ξ : ℝ)
      (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ),
      0 < B →
      B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) →
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B →
      ‖separatedCubeCoefficient
        (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
          (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
        (fun u => (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u) : ℝ))
        B ξ v‖ ≤ C*(Real.exp 1*B)^ε := by sorry
