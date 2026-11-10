-- Prove2me | Theorems.Thm_OAI_FirstPassCubeLabels_firstFrequencyDisk_uniform
-- name    : OAI.FirstPassCubeLabels.firstFrequencyDisk_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T23:38:42.355111+00:00
-- url     : https://prove2.me/theorems/c45d9a57-a1a1-4112-8812-bbf3eeb4a75d
-- title:
--   First Pass Cube Labels: first Frequency Disk uniform
-- statement:
--   The First Pass Cube Labels construction uses the first Frequency Disk uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L612-L660
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L612-L660

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Theorems.Thm_OAI_SecondPassArithmetic_columnLog_norm_upper
import Theorems.Thm_OAI_SecondPassArithmetic_outside_firstFrequencyDisk

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open SecondPassArithmetic (firstFrequencyDisk outside_firstFrequencyDisk columnLog_norm_upper)

theorem OAI.FirstPassCubeLabels.firstFrequencyDisk_uniform {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0)
    (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hNQ : Disjoint N Q) (hNB : Disjoint N B) (hQB : Disjoint Q B)
    (d : O) (hd : d≠0) (X₁ X₂ K P M₁ M₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hK : 0<K)
    (hN : columnLog p X₁ N≤M₁) (hQ : columnLog p X₂ Q≤M₂)
    (h : O) (hh : h∉firstFrequencyDisk
      (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)) :
    P/Real.exp (M₁+M₂)≤
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by sorry
