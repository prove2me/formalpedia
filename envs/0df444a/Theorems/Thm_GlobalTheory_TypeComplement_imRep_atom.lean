-- Prove2me | Theorems.Thm_GlobalTheory_TypeComplement_imRep_atom
-- name    : GlobalTheory.TypeComplement.imRep_atom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:46.614853+00:00
-- url     : https://prove2.me/theorems/8a12a25e-059e-4b0c-ae36-db41992c115e
-- title:
--   Type Complement: im Rep atom
-- statement:
--   The Type Complement construction uses the im Rep atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean#L53-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean#L53-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem GlobalTheory.TypeComplement.imRep_atom (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) {S : Subrepresentation ρ}
    (hS : IsAtom S) (hne : ∃ s ∈ S.toSubmodule, f s ≠ 0) :
    IsAtom (imRep f hf S) ∧
      Nonempty (S.toRepresentation.Equiv (imRep f hf S).toRepresentation) := by sorry
