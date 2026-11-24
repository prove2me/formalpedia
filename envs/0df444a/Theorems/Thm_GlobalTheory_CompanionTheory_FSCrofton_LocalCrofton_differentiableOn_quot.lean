-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_differentiableOn_quot
-- name    : GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.differentiableOn_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:01:44.40407+00:00
-- url     : https://prove2.me/theorems/cc63c72f-b0a1-4459-ac3f-b2f5faee73bb
-- title:
--   Local Crofton: differentiable On quot
-- statement:
--   The Local Crofton construction uses the differentiable On quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L99-L103

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

theorem GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.differentiableOn_quot {d : ℕ} {α : Type} (U : Set (V d)) (b : α → V d → ℂ)
    (hb : ∀ j, DifferentiableOn ℂ (b j) U) (j₀ : α) (hne : ∀ z ∈ U, b j₀ z ≠ 0) (j : α) :
    DifferentiableOn ℂ (fun v => b j v / b j₀ v) U := by sorry
