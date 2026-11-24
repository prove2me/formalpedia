-- Prove2me | Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_isUnit_natCast_of_coprime
-- name    : GlobalTheory.Proof.clears_idempotent_of_exponent_bound.isUnit_natCast_of_coprime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:00.040802+00:00
-- url     : https://prove2.me/theorems/8787f40f-9514-4703-bbd0-72c8151465b2
-- title:
--   clears idempotent of exponent bound: is Unit nat Cast of coprime
-- statement:
--   The clears idempotent of exponent bound construction uses the is Unit nat Cast of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L84-L95

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

theorem GlobalTheory.Proof.clears_idempotent_of_exponent_bound.isUnit_natCast_of_coprime {O : Type} [CommRing O] [IsLocalRing O] {m l : ℕ} (h : m.Coprime l)
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit (m : O) := by sorry
