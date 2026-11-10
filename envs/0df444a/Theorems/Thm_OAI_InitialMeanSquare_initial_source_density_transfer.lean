-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_source_density_transfer
-- name    : OAI.InitialMeanSquare.initial_source_density_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:35:05.178841+00:00
-- url     : https://prove2.me/theorems/b73b7f4b-acde-42e8-8713-dc12b83da234
-- title:
--   Initial Mean Square: initial source density transfer
-- statement:
--   The Initial Mean Square construction uses the initial source density transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L612-L649
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L612-L649

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
set_option autoImplicit false
open OAI
noncomputable section
open OAI.InitialMeanSquare
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
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem OAI.InitialMeanSquare.initial_source_density_transfer (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (T : Finset (O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (B : Frequency → ℝ) (J : ℕ) (S C : ℝ) (hS : 0 < S) (hC : 0 ≤ C)
    (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,S*B q ≤ C*tripleLogDensity J q) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,B (x,y,z)*
      sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (x,y,z)) ≤
    (C/S)*densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂ J := by sorry
