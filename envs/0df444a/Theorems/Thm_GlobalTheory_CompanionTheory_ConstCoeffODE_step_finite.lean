-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_step_finite
-- name    : GlobalTheory.CompanionTheory.ConstCoeffODE.step_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:48.93543+00:00
-- url     : https://prove2.me/theorems/93226f07-3f5d-40b7-a5c8-534e08057e9a
-- title:
--   Const Coeff ODE: step finite
-- statement:
--   The Const Coeff ODE construction uses the step finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L87-L89

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

theorem GlobalTheory.CompanionTheory.ConstCoeffODE.step_finite (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (step c S) := by sorry
