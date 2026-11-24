-- Prove2me | Theorems.Thm_GlobalTheory_HCA_weakSol_of_smooth
-- name    : GlobalTheory.HCA.weakSol_of_smooth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:00:04.658871+00:00
-- url     : https://prove2.me/theorems/3bfca77f-ddac-4e71-ac9b-283c2e74d541
-- title:
--   HCA: weak Sol of smooth
-- statement:
--   The HCA construction uses the weak Sol of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeakSolutionOfSmoothSolution.lean#L50-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeakSolutionOfSmoothSolution.lean#L50-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.weakSol_of_smooth :
    ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ),
      (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U →
      (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by sorry
