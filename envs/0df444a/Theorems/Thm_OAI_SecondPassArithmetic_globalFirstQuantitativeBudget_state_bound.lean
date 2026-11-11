-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalFirstQuantitativeBudget_state_bound
-- name    : OAI.SecondPassArithmetic.globalFirstQuantitativeBudget_state_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:48:31.937566+00:00
-- url     : https://prove2.me/theorems/c2a2efc7-d33a-496c-8357-c648eb0e4997
-- title:
--   Second Pass Arithmetic: global First Quantitative Budget state bound
-- statement:
--   The Second Pass Arithmetic construction uses the global First Quantitative Budget state bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DensityBudgets.lean#L98-L165
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DensityBudgets.lean#L98-L165

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoordinateLaplacian
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DensityBudgets
import Theorems.Thm_OAI_SecondPassIntegration_densityChildEnergy_from_canonical_state

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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy_from_canonical_state)

theorem OAI.SecondPassArithmetic.globalFirstQuantitativeBudget_state_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃ Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (windows : Fin 7 → ℝ → ℂ)
      (C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax : ℝ) (N J Ntail : ℕ),
      0≤C → 0≤Γ → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0 → |t|≤A₀) → (∀t,windows 6 t≠0 → |t|≤A₀) →
      (∀u,‖Ψ u‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (let source := globalQuantitativeSource p pool blocks K ell B F M H U side
       ∀a : RayCharacter×RayCharacter,∀r : FirstCoreIndex,
       ∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
       ∀ray : SecondRayIndex,∀q∈globalBinTriples p source side j,
       let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
       ∀s : ℝ,
       (canonicalLogEnergy p hp hcop hg pool (normHeightTwist (secondRayMinus Ψmode ray) s)
         (fixedTripleMask m q) (globalCanonicalLabels p source side q j)
         (orientedLogProfile true (windows 5)) (globalPooledColumnScale ell j)
         (globalLogRep j 8*Real.exp 1)≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖s‖)^(2*J)) ∧
       (canonicalLogEnergy p hp hcop hg pool (normHeightTwist (secondRayPlus Ψmode ray) s)
         (fixedTripleMask m q) (globalCanonicalLabels p source side q j)
         (orientedLogProfile false (windows 6)) (globalPooledColumnScale ell j)
         (globalLogRep j 8*Real.exp 1)≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε K ell B F M H U (N+1) (2*J) Ntail side ≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*((ell*B^3)*F)*
          ((B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H Ntail)+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (canonicalDensityConstant E J oldHeight*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))) := by sorry
