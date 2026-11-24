-- Prove2me | Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_coordAt_map
-- name    : GlobalTheory.Proof.clears_idempotent_of_exponent_bound.coordAt_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:51.767217+00:00
-- url     : https://prove2.me/theorems/796b83d3-3532-4528-bcd5-896fc781550d
-- title:
--   clears idempotent of exponent bound: coord At map
-- statement:
--   The clears idempotent of exponent bound construction uses the coord At map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L116-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean#L116-L126

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

theorem GlobalTheory.Proof.clears_idempotent_of_exponent_bound.coordAt_map {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] (w : O) (σ : E →+* K) (t : orderC (⊤ : Ideal (OF E)) ⊗[ℤ] O) :
    coordAt O 𝔣 σ (TensorProduct.map (mulMap hc) (LinearMap.mulLeft ℤ w) t) =
      σ (algebraMap (OF E) E c) * algebraMap O K w * coordAt O ⊤ σ t := by sorry
