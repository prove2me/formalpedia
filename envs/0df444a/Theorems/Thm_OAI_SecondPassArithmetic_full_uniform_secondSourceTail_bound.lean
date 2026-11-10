-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_full_uniform_secondSourceTail_bound
-- name    : OAI.SecondPassArithmetic.full_uniform_secondSourceTail_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T08:23:56.78778+00:00
-- url     : https://prove2.me/theorems/514f2d95-a03d-4238-a0e8-3981fe5f3a02
-- title:
--   Second Pass Arithmetic: full uniform second Source Tail bound
-- statement:
--   The Second Pass Arithmetic construction uses the full uniform second Source Tail bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean#L259-L298
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean#L259-L298

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply


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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem OAI.SecondPassArithmetic.full_uniform_secondSourceTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by sorry
