-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_prod_rowF
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_prod_rowF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:34.148517+00:00
-- url     : https://prove2.me/theorems/6ed42413-0a01-42e9-82ce-e16965481e0c
-- title:
--   Gauss Det: integrable prod row F
-- statement:
--   The Gauss Det construction uses the integrable prod row F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L202-L206

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

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_prod_rowF (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    Integrable (fun C : Fin d → β → ℂ => ∏ k, rowF G (σ k) (τ k) (C k)) := by sorry
