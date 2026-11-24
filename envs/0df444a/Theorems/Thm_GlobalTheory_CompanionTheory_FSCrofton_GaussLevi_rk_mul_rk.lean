-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_rk_mul_rk
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.rk_mul_rk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:26.740583+00:00
-- url     : https://prove2.me/theorems/8767f345-0b20-4fa5-8e96-705c142420fc
-- title:
--   Gauss Levi: rk mul rk
-- statement:
--   The Gauss Levi construction uses the rk mul rk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetLeviIntegral.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetLeviIntegral.lean#L26-L28

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

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.rk_mul_rk (f : β → ℂ) : rk f * rk f = ((nS f - 1 : ℝ) : ℂ) • rk f := by sorry
