-- Prove2me | Theorems.Thm_GlobalTheory_CondAway_clearsIdem_condQ_iff
-- name    : GlobalTheory.CondAway.clearsIdem_condQ_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:25:36.835092+00:00
-- url     : https://prove2.me/theorems/6516c0ad-e9ad-46f7-9593-c65f6dcd2d78
-- title:
--   Cond Away: clears Idem cond Q iff
-- statement:
--   The Cond Away construction uses the clears Idem cond Q iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentConductorIff.lean#L54-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentConductorIff.lean#L54-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIff
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
noncomputable section
open GlobalTheory GlobalTheory.CondAway
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.CondAway.clearsIdem_condQ_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O,
    ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D := by sorry
