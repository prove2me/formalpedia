-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_large_bin_geometry
-- name    : OAI.InitialMeanSquare.initial_large_bin_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:07:57.277474+00:00
-- url     : https://prove2.me/theorems/3eff0ccc-a8d1-43d2-9bf1-d9e4e6b8c963
-- title:
--   Initial Mean Square: initial large bin geometry
-- statement:
--   The Initial Mean Square construction uses the initial large bin geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/RetainedDensity.lean#L181-L236
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/RetainedDensity.lean#L181-L236

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
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
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)

theorem OAI.InitialMeanSquare.initial_large_bin_geometry {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z σ θ deltaLoss c : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hc : 1 ≤ c)
    (hR : R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)))
    (hj : j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b))
      (initialErrorRowBound a b Z (Z^(1+σ))))
    (hσ : 0 ≤ σ) (hmargin : deltaLoss+θ ≤ σ-(1 : ℝ)/20)
    (hlarge : Real.exp 2 ≤ Z ∧ c*Real.exp (initialErrorWindow a b) ≤ Z ∧
      initialPolynomialCap a b*Real.exp 2 ≤ Z ∧
      (Real.exp (initialErrorWindow a b))^2*Real.exp 2 ≤ Z ∧ c ≤ Z^deltaLoss)
    (hrad : initialRadial Z (Z^(1+σ)) (primeProductNorm p R) j ≤ Z^θ) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let lengthScale := initialLogLabel j
    let K := secondLogK j*Real.exp 2
    X ≤ Z^20 ∧ lengthScale ≤ Z^20 ∧ K ≤ Z^20 ∧ c*primeProductNorm p R ≤ Z^20 ∧
      X*lengthScale ≤ Z^2 ∧ K*(c*primeProductNorm p R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) := by sorry
