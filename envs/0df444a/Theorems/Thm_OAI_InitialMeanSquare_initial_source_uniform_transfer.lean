-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_source_uniform_transfer
-- name    : OAI.InitialMeanSquare.initial_source_uniform_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T09:49:24.657871+00:00
-- url     : https://prove2.me/theorems/af8c6a75-8359-40a9-99ee-9978f6e2a803
-- title:
--   Initial Mean Square: initial source uniform transfer
-- statement:
--   The Initial Mean Square construction uses the initial source uniform transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L180-L221
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L180-L221

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
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
open OAI.InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

theorem OAI.InitialMeanSquare.initial_source_uniform_transfer (ε : ℝ) (hε : 0<ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (M : Fin 7→ℝ)
    (hM : ∀j,0≤M j) (hV : ∀j x,V j x≠0→|x|≤M j) (N J : ℕ) :
    ∃ Cₐ : ℝ,0<Cₐ ∧ ∃ Cₛ : ℝ,0≤Cₛ ∧ ∀R:ℝ,0<R→∃b:𝓢(ℝ,ℂ),
      (∀t₁ t₂ t₃:ℝ,(1+R)^N*‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖≤
        Cₛ*FirstPassCubeLabels.firstLogDensity J t₁*FirstPassCubeLabels.firstLogDensity J t₂*
          FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
        (w : SecondExpansionData ι→ℂ) (A K : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O)
        (z ud ue uv kap : SecondExpansionData ι→ℝ) (X₁ X₂ : ℝ),
        0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
        (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
        (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
        (∀x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖≤A) →
        ‖initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖≤
          A*Cₐ*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖*
            sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by sorry
