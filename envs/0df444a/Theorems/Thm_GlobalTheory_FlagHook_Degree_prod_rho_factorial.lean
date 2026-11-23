-- Prove2me | Theorems.Thm_GlobalTheory_FlagHook_Degree_prod_rho_factorial
-- name    : GlobalTheory.FlagHook.Degree.prod_rho_factorial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:33.606034+00:00
-- url     : https://prove2.me/theorems/ff3c4a8d-dcf7-4956-a11a-303988179b22
-- title:
--   Degree: prod rho factorial
-- statement:
--   The Degree construction uses the prod rho factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagDegreeVandermonde.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagDegreeVandermonde.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
noncomputable section
open GlobalTheory GlobalTheory.FlagHook GlobalTheory.FlagHook.Degree

theorem GlobalTheory.FlagHook.Degree.prod_rho_factorial (N : ℕ) :
    ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) = ∏ m ∈ range N, (m.factorial : ℝ) := by sorry
