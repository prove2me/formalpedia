-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initialFrequencyCutoff_valid
-- name    : OAI.InitialMeanSquare.initialFrequencyCutoff_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:36:45.762198+00:00
-- url     : https://prove2.me/theorems/33281c92-e3b0-43be-ab42-bfd91b8e94c3
-- title:
--   Initial Mean Square: initial Frequency Cutoff valid
-- statement:
--   The Initial Mean Square construction uses the initial Frequency Cutoff valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L144-L178
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L144-L178

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
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.InitialMeanSquare.initialFrequencyCutoff_valid
    {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (m c d : O) (g : 𝓢(ℝ,ℂ)) (M Z Y T : ℝ)
    (hZ : 0<Z) (hY : 0<Y) (hgM : ∀t,g t≠0 → |t|≤M)
    (G E S R : Finset ι) (hEG : E⊆G) (hSR : Disjoint S R)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U)) S R≠0)
    (k : O) (hk : k∉initialFrequencyCutoff Z Y M T) :
    T≤(Y/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2))*‖eisEmbedding k‖^2 := by sorry
