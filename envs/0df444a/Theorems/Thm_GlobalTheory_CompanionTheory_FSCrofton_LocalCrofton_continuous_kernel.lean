-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_continuous_kernel
-- name    : GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.continuous_kernel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:41:09.932922+00:00
-- url     : https://prove2.me/theorems/e6ec600a-a9d6-44e4-9c7e-9fadf7655bae
-- title:
--   Local Crofton: continuous kernel
-- statement:
--   The Local Crofton construction uses the continuous kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L63-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L63-L81

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RandomSectionZeroCount
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

theorem GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.continuous_kernel (d : ℕ) (β : Type) [Fintype β] :
    Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      Real.exp (-∑ k, ‖∑ j, q.1 k j * q.2.1 j‖ ^ 2) *
        ‖(Matrix.of q.1 * (Matrix.of q.2.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2 := by sorry
