-- Prove2me | Theorems.Thm_OAI_FirstPassCubeLabels_cube_integral_norm_le_energy
-- name    : OAI.FirstPassCubeLabels.cube_integral_norm_le_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:36:21.229158+00:00
-- url     : https://prove2.me/theorems/7a52b419-80b4-4e66-84a7-a75c9acad182
-- title:
--   First Pass Cube Labels: cube integral norm le energy
-- statement:
--   The First Pass Cube Labels construction uses the cube integral norm le energy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean#L645-L711
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean#L645-L711

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.FirstPassCubeLabels.cube_integral_norm_le_energy {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F : Finset ι)
    (C₁ C₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => C₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => C₂ t S))
    (hn₁ : ∀ t S, ‖C₁ t S‖ = ‖C₁ 0 S‖)
    (hn₂ : ∀ t S, ‖C₂ t S‖ = ‖C₂ 0 S‖)
    (h : O) (b : 𝓢(ℝ, ℂ)) (a : ℂ) :
    ‖∫ t : ℝ, b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₁ t) true h) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₂ t) false h) := by sorry
