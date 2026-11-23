-- Prove2me | Theorems.Thm_GlobalTheory_FlagHook_Degree_signed_sum
-- name    : GlobalTheory.FlagHook.Degree.signed_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:53.609968+00:00
-- url     : https://prove2.me/theorems/d1d97694-d463-4ec2-b7a7-0e8eaa59c67e
-- title:
--   Degree: signed sum
-- statement:
--   The Degree construction uses the signed sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagDegreeVandermonde.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagDegreeVandermonde.lean#L19-L30

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

theorem GlobalTheory.FlagHook.Degree.signed_sum {N : ℕ} (v : Fin N → ℝ) :
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, v i ^ (N - 1 - ((σ i : Fin N) : ℕ)) =
      ∏ i, ∏ j ∈ Ioi i, (v i - v j) := by sorry
