-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_prime_product_moebius
-- name    : OAI.ActualEisensteinCubic.prime_product_moebius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:54.06608+00:00
-- url     : https://prove2.me/theorems/0b70e2f6-e2fa-438b-ae96-a82a791f346a
-- title:
--   Actual Eisenstein Cubic: prime product moebius
-- statement:
--   The Actual Eisenstein Cubic construction uses the prime product moebius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L369-L386
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L369-L386

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
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
open OAI.ActualEisensteinCubic

theorem OAI.ActualEisensteinCubic.prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by sorry
