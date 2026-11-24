-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_fockQ_hw
-- name    : GlobalTheory.FockHighestWeight.fockQ_hw
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:43.291036+00:00
-- url     : https://prove2.me/theorems/b297c696-0d66-49f3-ac6e-092f9883cb2c
-- title:
--   Fock Highest Weight: fock Q hw
-- statement:
--   The Fock Highest Weight construction uses the fock Q hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L158-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L158-L169

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

theorem GlobalTheory.FockHighestWeight.fockQ_hw : Formalism.GradedWeylDivisibility.FockQHW := by sorry
