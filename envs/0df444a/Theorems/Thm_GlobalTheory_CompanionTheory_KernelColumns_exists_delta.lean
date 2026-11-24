-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_exists_delta
-- name    : GlobalTheory.CompanionTheory.KernelColumns.exists_delta
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:57.069371+00:00
-- url     : https://prove2.me/theorems/cef11ad4-f3aa-45d6-9bdb-3931bce2637d
-- title:
--   Kernel Columns: exists delta
-- statement:
--   The Kernel Columns construction uses the exists delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecLimOf.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecLimOf.lean#L11-L28

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecLimOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns

theorem GlobalTheory.CompanionTheory.KernelColumns.exists_delta (c : ℝ≥0∞) (hc : c ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ^ 2 * c ≤ ENNReal.ofReal ε ^ 2 := by sorry
