-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurable_zeroCnt
-- name    : GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:08.827804+00:00
-- url     : https://prove2.me/theorems/5cfccf78-b2b3-4a40-a6bb-251f8d1bcd77
-- title:
--   FSCrofton: measurable zero Cnt
-- statement:
--   The FSCrofton construction uses the measurable zero Cnt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L189-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L189-L193

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]

theorem GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ),
    (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A →
      Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by sorry
