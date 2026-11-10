-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalChild_large_radial_bound
-- name    : OAI.SecondPassArithmetic.globalChild_large_radial_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T08:48:53.664066+00:00
-- url     : https://prove2.me/theorems/1b68e2f7-fc05-44b6-9e28-7fb9fd29a742
-- title:
--   Second Pass Arithmetic: global Child large radial bound
-- statement:
--   The Second Pass Arithmetic construction uses the global Child large radial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CubeBlocks.lean#L302-L358
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CubeBlocks.lean#L302-L358

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy)

theorem OAI.SecondPassArithmetic.globalChild_large_radial_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (η : ℝ) (hη : 0<η) :
    ∃ Cbox : ℝ,0<Cbox ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ)
      (C K ell B F M H U Z θ A₀ Vmax : ℝ) (N J : ℕ)
      (source : Finset (GlobalSecondData ι)) (side : Bool),
      0≤C → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z →
      0≤A₀ → 0≤Vmax → (∀ t,‖V₁ t‖≤Vmax) → (∀ t,‖V₂ t‖≤Vmax) →
      (∀ t,V₁ t≠0 → |t|≤A₀) → (∀ t,V₂ t≠0 → |t|≤A₀) →
      (∀ a,‖Ψ a‖≤1) → (∀ x∈source,x.source.frequency≠0) →
      (∀ x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀ x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∑ j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p source side j,
          globalDescentWeight C η 0 0 K ell B F (N+1) (2*J) j ray q *
          (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
            (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
            (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
      C*Cbox*(globalTerminalConstant A₀ Vmax*globalRayTripleConstant)*K*((ell*B^3)*F)*
        U^(deltaLoss+8*η)/Z^(θ*N) := by sorry
