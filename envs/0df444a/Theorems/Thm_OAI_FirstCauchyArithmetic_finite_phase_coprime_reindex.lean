-- Prove2me | Theorems.Thm_OAI_FirstCauchyArithmetic_finite_phase_coprime_reindex
-- name    : OAI.FirstCauchyArithmetic.finite_phase_coprime_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:26:00.916201+00:00
-- url     : https://prove2.me/theorems/ad97c067-d149-4ddd-84e2-1e210c56661b
-- title:
--   First Cauchy Arithmetic: finite phase coprime reindex
-- statement:
--   The First Cauchy Arithmetic construction uses the finite phase coprime reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RayCharacters.lean#L382-L437
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RayCharacters.lean#L382-L437

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
open ActualEisensteinCubic CoprimeMobiusExtension

theorem OAI.FirstCauchyArithmetic.finite_phase_coprime_reindex
    {ι R : Type*} [DecidableEq ι] [Fintype R] [DecidableEq R]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι)
    (σ : Finset ι → R) (phase : R → R → ℂ) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then phase (σ S) (σ T) *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : R × R, phase r.1 r.2 *
      ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
        star (supportConjugateSum P hg (B \ D)
          (fun U => if σ (D ∪ U) = r.1 then C₁ (D ∪ U) else 0) h) *
        supportConjugateSum P hg (B \ D)
          (fun V => if σ (D ∪ V) = r.2 then C₂ (D ∪ V) else 0) h := by sorry
