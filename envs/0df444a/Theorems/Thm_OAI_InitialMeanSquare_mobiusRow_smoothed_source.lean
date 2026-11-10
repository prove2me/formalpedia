-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_mobiusRow_smoothed_source
-- name    : OAI.InitialMeanSquare.mobiusRow_smoothed_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T08:49:21.384202+00:00
-- url     : https://prove2.me/theorems/b93282ca-9d5d-4d6a-8ddd-f9ef90fcc35c
-- title:
--   Initial Mean Square: mobius Row smoothed source
-- statement:
--   The Initial Mean Square construction uses the mobius Row smoothed source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CubeBlocks.lean#L406-L419
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CubeBlocks.lean#L406-L419

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
open scoped BigOperators Classical SchwartzMap
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})
variable (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀i,ringChar (OAI.InitialMeanSquare.O⧸Ideal.span {p i})≠2)
include hc

theorem OAI.InitialMeanSquare.mobiusRow_smoothed_source (F : Finset ι) (Ψ : O→*ℂ) (m : O)
    (H : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y)
    (K : Finset ι→Finset ι→Finset O) :
    (∑'z:O,W (‖eisEmbedding z‖^2/Y)*(‖mobiusRow p hg F Ψ m H z‖^2:ℝ))=
      truncatedSecondSource p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y (fun G E => (K G E).erase 0)+
      truncatedSecondZero p hg F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y K+
      secondSourceTail p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y K := by sorry
