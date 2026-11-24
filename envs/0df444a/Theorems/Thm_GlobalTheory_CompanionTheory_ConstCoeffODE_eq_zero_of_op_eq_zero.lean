-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_eq_zero_of_op_eq_zero
-- name    : GlobalTheory.CompanionTheory.ConstCoeffODE.eq_zero_of_op_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:51.272886+00:00
-- url     : https://prove2.me/theorems/ac6fed83-4ca4-4b16-95c6-9917cbea3d13
-- title:
--   Const Coeff ODE: eq zero of op eq zero
-- statement:
--   The Const Coeff ODE construction uses the eq zero of op eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L52-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L52-L77

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

theorem GlobalTheory.CompanionTheory.ConstCoeffODE.eq_zero_of_op_eq_zero (c : ℂ) {y : ℝ → ℂ} (hy : Differentiable ℝ y)
    (h : op c y = 0) (h0 : y 0 = 0) : y = 0 := by sorry
