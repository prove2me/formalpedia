-- Prove2me | Theorems.Thm_OAI_ConcretePrimeRowBridge_columnsUpTo_sum_eq_ideal_sum
-- name    : OAI.ConcretePrimeRowBridge.columnsUpTo_sum_eq_ideal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:18.387194+00:00
-- url     : https://prove2.me/theorems/b2e22bd1-332a-4349-8f82-69f28fe4517f
-- title:
--   Concrete Prime Row Bridge: columns Up To sum eq ideal sum
-- statement:
--   The Concrete Prime Row Bridge construction uses the columns Up To sum eq ideal sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean#L97-L108
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean#L97-L108

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
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
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem OAI.ConcretePrimeRowBridge.columnsUpTo_sum_eq_ideal_sum {q D : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) :
    (∑ x ∈ columnsUpTo D, columnWeight χ W x) =
      ∑ I ∈ idealsUpTo D,
        baseChangeWeight χ I * W (Ideal.absNorm I) := by sorry
