-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_inner_integral
-- name    : GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.inner_integral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:55.001027+00:00
-- url     : https://prove2.me/theorems/0c6f71d9-5e22-4d6d-b6de-d9e4606214a3
-- title:
--   Local Crofton: inner integral
-- statement:
--   The Local Crofton construction uses the inner integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L105-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RandomSectionZeroCount.lean#L105-L140

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

theorem GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.inner_integral (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d))
    (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (hne : ∀ z ∈ U, b j₀ z ≠ 0) (hAU : A ⊆ U) (hAm : MeasurableSet A)
    (g : {j : α // j ≠ j₀} → V d → ℂ) (hgA : ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    ∫⁻ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      ∫⁻ z in A, gW d {j : α // j ≠ j₀} C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * g j z‖ ^ 2) *
          ‖(Matrix.of C * (Matrix.of fun j a =>
            fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
              (EuclideanSpace.single a 1) : Matrix {j : α // j ≠ j₀} (Fin d) ℂ)).det‖ ^ 2) := by sorry
