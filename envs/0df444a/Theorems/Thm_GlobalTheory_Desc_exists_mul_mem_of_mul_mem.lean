-- Prove2me | Theorems.Thm_GlobalTheory_Desc_exists_mul_mem_of_mul_mem
-- name    : GlobalTheory.Desc.exists_mul_mem_of_mul_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:22.534046+00:00
-- url     : https://prove2.me/theorems/d5096244-5428-4cdc-99b2-d7183380d409
-- title:
--   Desc: exists mul mem of mul mem
-- statement:
--   The Desc construction uses the exists mul mem of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L124-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L124-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteTypeAwayOfAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Desc
open scoped TensorProduct

theorem GlobalTheory.Desc.exists_mul_mem_of_mul_mem {R C : Type} [CommRing R] [CommRing C] [IsDomain C] [Algebra R C]
    (B : Subalgebra R C) [IsNoetherianRing B] (x : C) (hx : x ≠ 0) (M : Submonoid R)
    (h : ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ B) :
    ∃ g ∈ M, ∀ c : C, x * c ∈ B → algebraMap R C g * c ∈ B := by sorry
