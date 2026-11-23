-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sum_irrChars_mul_apply
-- name    : GroundTheory.LocalField.sum_irrChars_mul_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:20.220982+00:00
-- url     : https://prove2.me/theorems/f6d182bd-7bbe-4fa3-84bd-d644a6fde07d
-- title:
--   Local Field: sum irr Chars mul apply
-- statement:
--   The Local Field construction uses the sum irr Chars mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L336-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L336-L341

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.sum_irrChars_mul_apply [DecidableEq G] (g : G) :
    ∑ ψ ∈ irrChars G, ψ 1 * ψ g = if g = 1 then (Nat.card G : ℂ) else 0 := by sorry
