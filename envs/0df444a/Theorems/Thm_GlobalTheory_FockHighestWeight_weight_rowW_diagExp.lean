-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_weight_rowW_diagExp
-- name    : GlobalTheory.FockHighestWeight.weight_rowW_diagExp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:56.008967+00:00
-- url     : https://prove2.me/theorems/2f7ab7fd-5412-412d-ae36-bfe91e97c814
-- title:
--   Fock Highest Weight: weight row W diag Exp
-- statement:
--   The Fock Highest Weight construction uses the weight row W diag Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L24-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L24-L40

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

theorem GlobalTheory.FockHighestWeight.weight_rowW_diagExp (ν : Fin n → ℕ) :
    Finsupp.weight (rowW r n) (diagExp r ν) = rowNu (r := r) ν := by sorry
