-- Prove2me | Theorems.Thm_GlobalTheory_CondAway_isUnit_absNorm_of_not_mem
-- name    : GlobalTheory.CondAway.isUnit_absNorm_of_not_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:44.493797+00:00
-- url     : https://prove2.me/theorems/86c1329f-5171-4f14-a9e9-b2cf00e161e0
-- title:
--   Cond Away: is Unit abs Norm of not mem
-- statement:
--   The Cond Away construction uses the is Unit abs Norm of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentConductorIff.lean#L13-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentConductorIff.lean#L13-L41

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

theorem GlobalTheory.CondAway.isUnit_absNorm_of_not_mem (q : HeightOneSpectrum (OF E)) (l : ℕ) (hl : l.Prime)
    (hq : (l : OF E) ∉ q.asIdeal) (O : Type) [CommRing O] [IsLocalRing O]
    (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit ((Ideal.absNorm q.asIdeal : ℕ) : O) := by sorry
