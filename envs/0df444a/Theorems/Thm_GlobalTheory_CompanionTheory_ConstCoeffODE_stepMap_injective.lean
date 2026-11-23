-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_stepMap_injective
-- name    : GlobalTheory.CompanionTheory.ConstCoeffODE.stepMap_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:42.752154+00:00
-- url     : https://prove2.me/theorems/055321cd-ee3b-4244-926d-63a0d70448bd
-- title:
--   Const Coeff ODE: step Map injective
-- statement:
--   The Const Coeff ODE construction uses the step Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L79-L85

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

theorem GlobalTheory.CompanionTheory.ConstCoeffODE.stepMap_injective (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) :
    Function.Injective (stepMap c S) := by sorry
