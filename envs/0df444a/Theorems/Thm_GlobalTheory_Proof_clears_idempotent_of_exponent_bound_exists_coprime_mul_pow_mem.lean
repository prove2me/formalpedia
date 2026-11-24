-- Prove2me | Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_exists_coprime_mul_pow_mem
-- name    : GlobalTheory.Proof.clears_idempotent_of_exponent_bound.exists_coprime_mul_pow_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:39.555301+00:00
-- url     : https://prove2.me/theorems/49da6d6b-274f-43bd-9cbe-b5bafb2f99de
-- title:
--   clears idempotent of exponent bound: exists coprime mul pow mem
-- statement:
--   The clears idempotent of exponent bound construction uses the exists coprime mul pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L49-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L49-L82

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

theorem GlobalTheory.Proof.clears_idempotent_of_exponent_bound.exists_coprime_mul_pow_mem {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) {l : ℕ} (hl : l.Prime) {k : ℕ}
    (hk : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) :
    ∃ m : ℕ, m.Coprime l ∧ ((m : OF E) * (l : OF E) ^ k) ∈ 𝔣 := by sorry
