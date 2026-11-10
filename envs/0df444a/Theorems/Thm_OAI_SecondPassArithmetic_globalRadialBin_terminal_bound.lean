-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalRadialBin_terminal_bound
-- name    : OAI.SecondPassArithmetic.globalRadialBin_terminal_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T05:50:09.772508+00:00
-- url     : https://prove2.me/theorems/0fc82b13-41a9-479f-bcc7-500594c3c530
-- title:
--   Second Pass Arithmetic: global Radial Bin terminal bound
-- statement:
--   The Second Pass Arithmetic construction uses the global Radial Bin terminal bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GlobalScales.lean#L472-L565
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GlobalScales.lean#L472-L565

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)

theorem OAI.SecondPassArithmetic.globalRadialBin_terminal_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (V₁ V₂ : ℝ → ℂ) (C ε θ₁ θ₂ K ell B F A₀ M : ℝ) (N J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hA₀ : 0 ≤ A₀) (hM : 0 ≤ M)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ M) (hV₂ : ∀ t,‖V₂ t‖ ≤ M)
    (hVs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A₀) (hVs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A₀)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hJ : globalLogRep j 4 ≤ B^2) :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
    (C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (globalTerminalConstant A₀ M*globalRayTripleConstant)*K*((ell*B^3)*F)) /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by sorry
