-- Prove2me | Theorems.Thm_GlobalTheory_NonzeroSmulMembership_exists_ne_zero_smul_mem
-- name    : GlobalTheory.NonzeroSmulMembership.exists_ne_zero_smul_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:30.143136+00:00
-- url     : https://prove2.me/theorems/445850bf-b846-4bb4-9f9f-a5b2114fbfce
-- title:
--   Nonzero Smul Membership: exists ne zero smul mem
-- statement:
--   The Nonzero Smul Membership construction uses the exists ne zero smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsExtraLast.lean#L5-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsExtraLast.lean#L5-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsExtraLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroSmulMembership

theorem GlobalTheory.NonzeroSmulMembership.exists_ne_zero_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (x : Fin n → E) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by sorry
