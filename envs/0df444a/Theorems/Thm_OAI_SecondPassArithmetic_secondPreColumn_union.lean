-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_secondPreColumn_union
-- name    : OAI.SecondPassArithmetic.secondPreColumn_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:16:58.840196+00:00
-- url     : https://prove2.me/theorems/52e2075d-5bfe-45ca-90a6-0f50f171d00e
-- title:
--   Second Pass Arithmetic: second Pre Column union
-- statement:
--   The Second Pass Arithmetic construction uses the second Pre Column union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean#L551-L581
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean#L551-L581

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstPassage
import Theorems.Thm_OAI_FirstPassCubeLabels_mask_mul
import Theorems.Thm_OAI_FirstPassCubeLabels_mask_union
import Theorems.Thm_OAI_FirstPassCubeLabels_row_union
import Theorems.Thm_OAI_PoissonChildCRT_mask_mul

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels (row_union mask_union mask_mul)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem OAI.SecondPassArithmetic.secondPreColumn_union
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m r c d e k : O) (H : Finset ι → ℂ)
    (V N : Finset ι) (hd : Disjoint V N) :
    secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k H (V ∪ N) =
      secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
        (fun U => H (V ∪ U)) N := by sorry
