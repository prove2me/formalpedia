-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_rowF
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_rowF
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:26.705053+00:00
-- url     : https://prove2.me/theorems/ccaf74d1-e182-4551-92e1-9e61d1080d2e
-- title:
--   Gauss Det: integral row F
-- statement:
--   The Gauss Det construction uses the integral row F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean#L129-L140

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

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) :
    ∫ r, rowF G a c r = (Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) c a := by sorry
