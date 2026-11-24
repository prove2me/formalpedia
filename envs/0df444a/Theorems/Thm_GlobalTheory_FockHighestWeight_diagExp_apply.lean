-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_diagExp_apply
-- name    : GlobalTheory.FockHighestWeight.diagExp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:49.215927+00:00
-- url     : https://prove2.me/theorems/a83adfd7-01b5-4561-862f-b8108c684d9f
-- title:
--   Fock Highest Weight: diag Exp apply
-- statement:
--   The Fock Highest Weight construction uses the diag Exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L15-L16

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

theorem GlobalTheory.FockHighestWeight.diagExp_apply (ν : Fin n → ℕ) (a : Fin r) (s : Fin n) :
    diagExp r ν (a, s) = if a.val = s.val then ν s else 0 := by sorry
