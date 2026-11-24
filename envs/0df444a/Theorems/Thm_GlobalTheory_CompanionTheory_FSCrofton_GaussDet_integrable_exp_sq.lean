-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_exp_sq
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_exp_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:04.545238+00:00
-- url     : https://prove2.me/theorems/556bf2b9-1ade-4dcf-a746-6e4d86a54b4d
-- title:
--   Gauss Det: integrable exp sq
-- statement:
--   The Gauss Det construction uses the integrable exp sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L23-L24

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

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_exp_sq : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by sorry
