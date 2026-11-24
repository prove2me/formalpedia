-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_eval_idFrame_eq_coeff
-- name    : GlobalTheory.FockHighestWeight.eval_idFrame_eq_coeff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:39.103798+00:00
-- url     : https://prove2.me/theorems/81e7ee73-f97d-4793-b8ba-422822b22c63
-- title:
--   Fock Highest Weight: eval id Frame eq coeff
-- statement:
--   The Fock Highest Weight construction uses the eval id Frame eq coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L105-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L105-L121

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}

theorem GlobalTheory.FockHighestWeight.eval_idFrame_eq_coeff {R : Type*} [CommRing R] {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) R}
    (hcol : ∀ m ∈ F.support, ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) :
    eval (idFrame R r n) F = coeff (diagExp r ν) F := by sorry
