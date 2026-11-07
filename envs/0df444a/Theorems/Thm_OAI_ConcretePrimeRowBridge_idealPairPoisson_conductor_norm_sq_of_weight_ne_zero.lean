-- Prove2me | Theorems.Thm_OAI_ConcretePrimeRowBridge_idealPairPoisson_conductor_norm_sq_of_weight_ne_zero
-- name    : OAI.ConcretePrimeRowBridge.idealPairPoisson_conductor_norm_sq_of_weight_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:57.977149+00:00
-- url     : https://prove2.me/theorems/bb9b47d4-07d0-41ec-a11c-345ce083caa5
-- title:
--   Concrete Prime Row Bridge: ideal Pair Poisson conductor norm sq of weight ne zero
-- statement:
--   The Concrete Prime Row Bridge construction uses the ideal Pair Poisson conductor norm sq of weight ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ActiveConductor.lean#L628-L642
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ActiveConductor.lean#L628-L642

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
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
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem OAI.ConcretePrimeRowBridge.idealPairPoisson_conductor_norm_sq_of_weight_ne_zero
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hwI : baseChangeWeight χ I ≠ 0) (hwJ : baseChangeWeight χ J ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus
      (activePrimes (fun i : primePool F => i.val) (idealSupport F I) (idealSupport F J)))‖ ^ 2 *
      (Ideal.absNorm (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) : ℝ) ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by sorry
