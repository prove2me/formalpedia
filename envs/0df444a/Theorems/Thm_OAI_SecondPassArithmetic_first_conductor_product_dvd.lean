-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_first_conductor_product_dvd
-- name    : OAI.SecondPassArithmetic.first_conductor_product_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T09:49:35.272524+00:00
-- url     : https://prove2.me/theorems/1378dcdd-f560-449e-bd97-cdd98998dca6
-- title:
--   Second Pass Arithmetic: first conductor product dvd
-- statement:
--   The Second Pass Arithmetic construction uses the first conductor product dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L471-L481
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L471-L481

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (bit conductorExponent dilationExponent retained parity evenDouble
  primeProduct primeProductNorm aLabel dilationLabel jLabel j2Label squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.SecondPassArithmetic.O)
variable [∀ i,(Ideal.span {p i}).IsMaximal]
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal]

theorem OAI.SecondPassArithmetic.first_conductor_product_dvd (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) :
    (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)*
      dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂*jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣
      aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2 := by sorry
