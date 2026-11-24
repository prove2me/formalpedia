-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurePreserving_joinEntry
-- name    : GlobalTheory.CompanionTheory.FSCrofton.measurePreserving_joinEntry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:37.905874+00:00
-- url     : https://prove2.me/theorems/78347096-f00c-4ef7-aa51-d2541d3698ed
-- title:
--   FSCrofton: measure Preserving join Entry
-- statement:
--   The FSCrofton construction uses the measure Preserving join Entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralSplitColumn.lean#L15-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralSplitColumn.lean#L15-L41

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumn
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

theorem GlobalTheory.CompanionTheory.FSCrofton.measurePreserving_joinEntry {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : ℂ × ({j : α // j ≠ j₀} → ℂ) =>
        (fun j => if h : j = j₀ then p.1 else p.2 ⟨j, h⟩ : α → ℂ))
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      (Measure.pi fun _ : α => (volume : Measure ℂ)) := by sorry
