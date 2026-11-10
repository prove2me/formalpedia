-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_cubeDivisorKey_injective_on_product
-- name    : OAI.SecondPassArithmetic.cubeDivisorKey_injective_on_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:53:30.402891+00:00
-- url     : https://prove2.me/theorems/87e382d0-6077-4777-9d1a-0df94c6dcf42
-- title:
--   Second Pass Arithmetic: cube Divisor Key injective on product
-- statement:
--   The Second Pass Arithmetic construction uses the cube Divisor Key injective on product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/SmoothTests.lean#L602-L627
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/SmoothTests.lean#L602-L627

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel b0Label j2Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
variable (hp : ∀ i,p i≠0)
include hp
variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem OAI.SecondPassArithmetic.cubeDivisorKey_injective_on_product {x y : CubeCoordinates ι}
    (hx : x.Admissible) (hy : y.Admissible)
    (hprod : cubeProductIdeal p x=cubeProductIdeal p y)
    (hk : cubeDivisorKey p x=cubeDivisorKey p y) : x=y := by sorry
