-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_step_finrank_le
-- name    : GlobalTheory.CompanionTheory.ConstCoeffODE.step_finrank_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:38.558432+00:00
-- url     : https://prove2.me/theorems/c56c42bd-3bff-468e-855d-905a680228e0
-- title:
--   Const Coeff ODE: step finrank le
-- statement:
--   The Const Coeff ODE construction uses the step finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L91-L95

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialPolynomialSolutionSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConstCoeffODE

theorem GlobalTheory.CompanionTheory.ConstCoeffODE.step_finrank_le (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    Module.finrank ℂ (step c S) ≤ Module.finrank ℂ S + 1 := by sorry
