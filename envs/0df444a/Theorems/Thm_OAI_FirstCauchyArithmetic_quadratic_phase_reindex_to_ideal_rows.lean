-- Prove2me | Theorems.Thm_OAI_FirstCauchyArithmetic_quadratic_phase_reindex_to_ideal_rows
-- name    : OAI.FirstCauchyArithmetic.quadratic_phase_reindex_to_ideal_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:24:30.078068+00:00
-- url     : https://prove2.me/theorems/26f5ac57-e2e1-421c-aac0-18b573ed6262
-- title:
--   First Cauchy Arithmetic: quadratic phase reindex to ideal rows
-- statement:
--   The First Cauchy Arithmetic construction uses the quadratic phase reindex to ideal rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RayCharacters.lean#L691-L723
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RayCharacters.lean#L691-L723

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
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
open scoped BigOperators Classical
open OAI.FirstCauchyArithmetic
open ActualEisensteinCubic ConcretePrimeRowBridge

theorem OAI.FirstCauchyArithmetic.quadratic_phase_reindex_to_ideal_rows
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then MixedCrossSeparation.quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter,
      RayFourExpansion.crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => star (supportRay p r.1 (recoveredSupport P (B \ D) I)) *
            C₁ (D ∪ recoveredSupport P (B \ D) I)) h) *
        conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => supportRay p r.2 (recoveredSupport P (B \ D) I) *
            C₂ (D ∪ recoveredSupport P (B \ D) I)) h := by sorry
