-- Prove2me | Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_exists_not_mem_mul_pow_mem
-- name    : GlobalTheory.Proof.clears_idempotent_of_exponent_bound.exists_not_mem_mul_pow_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:02.279797+00:00
-- url     : https://prove2.me/theorems/3048c600-5a28-4c16-b474-d4a7cd19d719
-- title:
--   clears idempotent of exponent bound: exists not mem mul pow mem
-- statement:
--   The clears idempotent of exponent bound construction uses the exists not mem mul pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L10-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.clears_idempotent_of_exponent_bound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.Proof.clears_idempotent_of_exponent_bound.exists_not_mem_mul_pow_mem {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (OF E)) {c : OF E}
    (hc : c ∈ v.asIdeal) {k : ℕ} (hk : expIn 𝔣 v ≤ k) : ∃ x : OF E, x ∉ v.asIdeal ∧ x * c ^ k ∈ 𝔣 := by sorry
