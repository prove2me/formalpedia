-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_A3_unramified_fixed_denominator_local_character
-- name    : OAI.ActualEisensteinCubic.A3_unramified_fixed_denominator_local_character
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:22.349209+00:00
-- url     : https://prove2.me/theorems/7f353fc8-d2ef-4d3c-8fa4-5cde51d14944
-- title:
--   Actual Eisenstein Cubic: A3 unramified fixed denominator local character
-- statement:
--   The Actual Eisenstein Cubic construction uses the A3 unramified fixed denominator local character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactWeights.lean#L415-L427
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactWeights.lean#L415-L427

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
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
open OAI.ActualEisensteinCubic
open ShortDraftCusp

theorem OAI.ActualEisensteinCubic.A3_unramified_fixed_denominator_local_character
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b c d : O) (hdet : a * d - b * c = 1)
    (hd : d ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (-b)) *
      cubicChar P hgood (Ideal.Quotient.mk P c) = 1 := by sorry
