-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_continuous_hf
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussDet.continuous_hf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:07.817548+00:00
-- url     : https://prove2.me/theorems/fb672b69-c9c7-4a39-a192-1f996ee2fd69
-- title:
--   Gauss Det: continuous hf
-- statement:
--   The Gauss Det construction uses the continuous hf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L32-L34

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

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussDet.continuous_hf (p q : Prop) [Decidable p] [Decidable q] : Continuous (hf p q) := by sorry
