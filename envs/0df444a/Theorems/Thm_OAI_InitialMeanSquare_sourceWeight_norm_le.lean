-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_sourceWeight_norm_le
-- name    : OAI.InitialMeanSquare.sourceWeight_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T09:31:39.834408+00:00
-- url     : https://prove2.me/theorems/7ccd2059-6f9f-4e61-88ab-45067dcd3f55
-- title:
--   Initial Mean Square: source Weight norm le
-- statement:
--   The Initial Mean Square construction uses the source Weight norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean#L98-L108
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean#L98-L108

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (elementNorm)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem OAI.InitialMeanSquare.sourceWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex) (Z H : ℝ) (x : SecondExpansionData ι)
    (hZ : 0<Z) (hH : 0≤H)
    (hΨG : ‖Ψ (∏i∈x.sourceCommon,p i)‖≤1) (hΨV : ‖Ψ (∏i∈x.overlap,p i)‖≤1) :
    ‖sourceWeight p hp hcop hg Ψ m ray Z H x‖≤
      H*elementNorm (secondExpansionQuotient p x)/Z^2*‖secondRayCoefficient ray‖ := by sorry
