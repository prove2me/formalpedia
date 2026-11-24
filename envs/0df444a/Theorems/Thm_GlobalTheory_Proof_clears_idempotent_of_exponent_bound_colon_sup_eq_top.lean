-- Prove2me | Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_colon_sup_eq_top
-- name    : GlobalTheory.Proof.clears_idempotent_of_exponent_bound.colon_sup_eq_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:33.307969+00:00
-- url     : https://prove2.me/theorems/42c11dfd-bcf6-4aab-8c63-ebec63df19c0
-- title:
--   clears idempotent of exponent bound: colon sup eq top
-- statement:
--   The clears idempotent of exponent bound construction uses the colon sup eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L28-L41

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

theorem GlobalTheory.Proof.clears_idempotent_of_exponent_bound.colon_sup_eq_top {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) {l : ℕ} (hl : l ≠ 0) {k : ℕ}
    (hk : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) :
    𝔣.colon {((l : OF E) ^ k)} ⊔ Ideal.span {(l : OF E)} = ⊤ := by sorry
