-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_eval_idFrame_hw
-- name    : GlobalTheory.FockHighestWeight.eval_idFrame_hw
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:40.529831+00:00
-- url     : https://prove2.me/theorems/b2b10af5-08ad-4262-9cda-6faea514513f
-- title:
--   Fock Highest Weight: eval id Frame hw
-- statement:
--   The Fock Highest Weight construction uses the eval id Frame hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L123-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L123-L133

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

theorem GlobalTheory.FockHighestWeight.eval_idFrame_hw {R : Type*} [CommRing R] (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by sorry
