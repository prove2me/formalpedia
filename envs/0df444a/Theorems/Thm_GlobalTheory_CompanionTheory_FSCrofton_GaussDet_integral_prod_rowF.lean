-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_prod_rowF
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_prod_rowF
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:10.465857+00:00
-- url     : https://prove2.me/theorems/c00d09a6-b525-4e20-a2ef-d6e3dc886a2f
-- title:
--   Gauss Det: integral prod row F
-- statement:
--   The Gauss Det construction uses the integral prod row F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L208-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L208-L212

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

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_prod_rowF (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    ∫ C : Fin d → β → ℂ, ∏ k, rowF G (σ k) (τ k) (C k) =
      ∏ k, ((Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) (τ k) (σ k)) := by sorry
