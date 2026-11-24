-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_fsLevi_eq
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.fsLevi_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:31.363952+00:00
-- url     : https://prove2.me/theorems/6fc63ad3-7069-47b6-94b5-ae658ca1cb8d
-- title:
--   Gauss Levi: fs Levi eq
-- statement:
--   The Gauss Levi construction uses the fs Levi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetLeviIntegral.lean#L170-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetLeviIntegral.lean#L170-L185

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
open Matrix
variable {β : Type} [Fintype β] [DecidableEq β]

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.fsLevi_eq {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    fsLevi f F = ((1 / nS f : ℝ) : ℂ) • ((rM f * F)ᴴ * (rM f * F))ᵀ := by sorry
