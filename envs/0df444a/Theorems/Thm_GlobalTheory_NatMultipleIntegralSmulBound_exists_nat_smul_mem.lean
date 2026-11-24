-- Prove2me | Theorems.Thm_GlobalTheory_NatMultipleIntegralSmulBound_exists_nat_smul_mem
-- name    : GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:51.322444+00:00
-- url     : https://prove2.me/theorems/96015dab-4d95-4f5b-8c0c-b8266f7a1661
-- title:
--   Nat Multiple Integral Smul Bound: exists nat smul mem
-- statement:
--   The Nat Multiple Integral Smul Bound construction uses the exists nat smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNatSmulLe.lean#L16-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNatSmulLe.lean#L16-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatSmulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMultipleIntegralSmulBound
open NumberField

theorem GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L' : Submodule (RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by sorry
