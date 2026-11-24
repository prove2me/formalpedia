-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_hf
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_hf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:24.460843+00:00
-- url     : https://prove2.me/theorems/b8003f05-80e4-4b66-b864-074b538e1ef6
-- title:
--   Gauss Det: integrable hf
-- statement:
--   The Gauss Det construction uses the integrable hf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L36-L46

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

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_hf (p q : Prop) [Decidable p] [Decidable q] : Integrable (hf p q) := by sorry
