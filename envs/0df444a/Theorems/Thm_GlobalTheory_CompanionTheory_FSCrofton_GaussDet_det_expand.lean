-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_det_expand
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussDet.det_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:34.008803+00:00
-- url     : https://prove2.me/theorems/f28c6db9-eb06-458c-9359-9f6f9194d487
-- title:
--   Gauss Det: det expand
-- statement:
--   The Gauss Det construction uses the det expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L142-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L142-L176

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.GaussDet
variable {β : Type} [Fintype β] [DecidableEq β]
variable {d : ℕ}

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussDet.det_expand (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) :
    ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, rowF G (σ k) (τ k) (C k) := by sorry
