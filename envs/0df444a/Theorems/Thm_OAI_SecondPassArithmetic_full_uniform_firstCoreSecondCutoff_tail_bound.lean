-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_full_uniform_firstCoreSecondCutoff_tail_bound
-- name    : OAI.SecondPassArithmetic.full_uniform_firstCoreSecondCutoff_tail_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T08:23:23.025705+00:00
-- url     : https://prove2.me/theorems/56b3d31c-7734-41ce-867e-a79f6e5d430f
-- title:
--   Second Pass Arithmetic: full uniform first Core Second Cutoff tail bound
-- statement:
--   The Second Pass Arithmetic construction uses the full uniform first Core Second Cutoff tail bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean#L300-L347
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean#L300-L347

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

theorem OAI.SecondPassArithmetic.full_uniform_firstCoreSecondCutoff_tail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g V W : 𝓢(ℝ, ℂ))
      (negative : Bool) (t X Y M H : ℝ),
      0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
      ∑ G ∈ (F\D).powerset, ∑ E : G.powerset,
        ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg (F\D) G Ψ Ψ m c d (fun S => Hbase (G∪S)) (fun S => Hbase (G∪S))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by sorry
