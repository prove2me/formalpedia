-- Prove2me | Theorems.Thm_OAI_LocalReflectionBrackets_actual_bracket_four_divisibility_split
-- name    : OAI.LocalReflectionBrackets.actual_bracket_four_divisibility_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:53:37.877632+00:00
-- url     : https://prove2.me/theorems/48321a46-2531-4d06-94ce-ad8d0fec9e20
-- title:
--   Local Reflection Brackets: actual bracket four divisibility split
-- statement:
--   The Local Reflection Brackets construction uses the actual bracket four divisibility split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ReflectionBrackets.lean#L141-L147
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ReflectionBrackets.lean#L141-L147

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
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
open OAI.LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]
open ActualEisensteinCubic
attribute [local instance] OAI.LocalReflectionBrackets.quotientFieldBounds
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintypeBounds

theorem OAI.LocalReflectionBrackets.actual_bracket_four_divisibility_split (p : O) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (n b : O) :
    bracket (canonicalSextic (Ideal.span {p}) hgood) 4 (Ideal.Quotient.mk (Ideal.span {p}) (n * b ^ 3)) =
      -(rootCard (O ⧸ Ideal.span {p}) : ℂ)⁻¹ +
      (rootCard (O ⧸ Ideal.span {p}) : ℂ) * (if p ∣ n then 1 else 0) +
      (rootCard (O ⧸ Ideal.span {p}) : ℂ) * (if ¬p ∣ n ∧ p ∣ b then 1 else 0) := by sorry
