-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_solutions_mem_finite
-- name    : GlobalTheory.CompanionTheory.ConstCoeffODE.solutions_mem_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:06.626891+00:00
-- url     : https://prove2.me/theorems/d0ed7a68-8600-49ec-8217-6f4e7fd0ff34
-- title:
--   Const Coeff ODE: solutions mem finite
-- statement:
--   The Const Coeff ODE construction uses the solutions mem finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L97-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialPolynomialSolutionSpace.lean#L97-L139

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

theorem GlobalTheory.CompanionTheory.ConstCoeffODE.solutions_mem_finite :
    ∀ l : List ℂ, ∃ S : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ l.length ∧
      ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (D : Module.End ℂ X) (ev : X →ₗ[ℂ] (ℝ → ℂ)),
        (∀ x t, HasDerivAt (ev x) (ev (D x) t) t) →
          ∀ x, ev ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod x) = 0 → ev x ∈ S := by sorry
