-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_lowerTri_of_interlaced
-- name    : GlobalTheory.FockHighestWeight.lowerTri_of_interlaced
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:42.263195+00:00
-- url     : https://prove2.me/theorems/331e3ca4-9291-4445-a82c-9ea4ef55dcf7
-- title:
--   Fock Highest Weight: lower Tri of interlaced
-- statement:
--   The Fock Highest Weight construction uses the lower Tri of interlaced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L56-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L56-L74

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

theorem GlobalTheory.FockHighestWeight.lowerTri_of_interlaced {m : Fin r × Fin n →₀ ℕ} (hm : Interlaced m) : LowerTri m := by sorry
