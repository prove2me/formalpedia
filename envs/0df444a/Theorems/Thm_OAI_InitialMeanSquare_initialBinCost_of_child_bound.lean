-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initialBinCost_of_child_bound
-- name    : OAI.InitialMeanSquare.initialBinCost_of_child_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T15:20:52.727724+00:00
-- url     : https://prove2.me/theorems/8089c29c-3ea8-4ee6-b103-d0169bdca373
-- title:
--   Initial Mean Square: initial Bin Cost of child bound
-- statement:
--   The Initial Mean Square construction uses the initial Bin Cost of child bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/BranchScaling.lean#L347-L404
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/BranchScaling.lean#L347-L404

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem OAI.InitialMeanSquare.initialBinCost_of_child_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hchild : ∀ q,
      let s := secondLogSector p ∅ F K R Z M j
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X q ≤
        (Cchild*(X*initialLogLabel j))*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/Z)*Real.exp 2*Cchild*Cₛ*(∫ t : ℝ,firstLogDensity 0 t)^3)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by sorry
