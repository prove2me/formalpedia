-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_gW_joinCol
-- name    : GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.gW_joinCol
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:44.429874+00:00
-- url     : https://prove2.me/theorems/56551300-ff67-4e53-ab68-dfdf5e2b5684
-- title:
--   Local Crofton: g W join Col
-- statement:
--   The Local Crofton construction uses the g W join Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L30-L44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RandomSectionZeroCount
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton

theorem GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.gW_joinCol {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    gW d α (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) := by sorry
