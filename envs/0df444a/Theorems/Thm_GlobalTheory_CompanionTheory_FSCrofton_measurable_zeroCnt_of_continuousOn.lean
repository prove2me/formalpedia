-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurable_zeroCnt_of_continuousOn
-- name    : GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt_of_continuousOn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:38.574796+00:00
-- url     : https://prove2.me/theorems/f4e0d7f0-2032-47e7-ae32-458173dfc7d3
-- title:
--   FSCrofton: measurable zero Cnt of continuous On
-- statement:
--   The FSCrofton construction uses the measurable zero Cnt of continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L181-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L181-L187

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

theorem GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt_of_continuousOn [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by sorry
