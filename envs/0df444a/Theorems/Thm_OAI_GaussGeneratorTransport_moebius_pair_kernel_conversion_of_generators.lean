-- Prove2me | Theorems.Thm_OAI_GaussGeneratorTransport_moebius_pair_kernel_conversion_of_generators
-- name    : OAI.GaussGeneratorTransport.moebius_pair_kernel_conversion_of_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:55.634859+00:00
-- url     : https://prove2.me/theorems/174cff8d-ea49-429f-929f-808114469dab
-- title:
--   Gauss Generator Transport: moebius pair kernel conversion of generators
-- statement:
--   The Gauss Generator Transport construction uses the moebius pair kernel conversion of generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/MixedConversion.lean#L316-L332
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/MixedConversion.lean#L316-L332

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion

theorem OAI.GaussGeneratorTransport.moebius_pair_kernel_conversion_of_generators
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (p : ι → O) (hP : ∀ i, P i = Ideal.span {p i}) (hp : ∀ i, p i ≠ 0)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    letI : ∀ i, (Ideal.span {p i}).IsMaximal := fun i =>
      (hP i) ▸ (inferInstance : (P i).IsMaximal)
    let hg : ∀ i, lambda ∉ Ideal.span {p i} := fun i => (hP i) ▸ hgood i
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, P i) : ℂ)) *
      squarefreePairPoissonKernel P hinj hgood S T W scale =
      convertedPairPoissonKernel p hp hg S T W scale := by sorry
